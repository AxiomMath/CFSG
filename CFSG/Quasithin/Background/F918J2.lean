module

public import CFSG.Quasithin.Background.B69Red
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Background.InternalSecBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section General

theorem insp5a_sec_mul_pow_mem {G : Type*} [Group G] {K : Subgroup G} {k σ : G} (hk : k ∈ K)
    (hσ : σ ∈ Subgroup.normalizer (K : Set G)) (n : ℕ) : ∃ k' ∈ K, (k * σ) ^ n = k' * σ ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', hn⟩ := ih
    have hσn : σ ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hσ n
    have hc : σ ^ n * k * (σ ^ n)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hσn k).mp hk
    refine ⟨k' * (σ ^ n * k * (σ ^ n)⁻¹), K.mul_mem hk' hc, ?_⟩
    rw [pow_succ, hn]
    group

theorem insp5a_sec_exists_ne_of_commV_eq {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {V : Subgroup W} (hcomm : commV L = V) (hns : ¬ Group.IsSolvable ↥L) :
    ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  by_contra hcon
  push Not at hcon
  apply hns
  have hd : ∀ (x : ↥L) (w : W), (x : MulAut W) w * w⁻¹ ∈ V := fun x w => by
    rw [← hcomm]
    exact Subgroup.subset_closure ⟨x, x.2, w, rfl⟩
  have h1 : ∀ (x y : ↥L) (w : W),
      (x : MulAut W) ((y : MulAut W) w) = ((y : MulAut W) w * w⁻¹) * (x : MulAut W) w := by
    intro x y w
    have hfix : (x : MulAut W) ((y : MulAut W) w * w⁻¹) = (y : MulAut W) w * w⁻¹ :=
      hcon x x.2 _ (hd y w)
    calc (x : MulAut W) ((y : MulAut W) w)
        = (x : MulAut W) (((y : MulAut W) w * w⁻¹) * w) := by rw [inv_mul_cancel_right]
      _ = (x : MulAut W) ((y : MulAut W) w * w⁻¹) * (x : MulAut W) w := map_mul _ _ _
      _ = _ := by rw [hfix]
  refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
  ext w
  show (a : MulAut W) ((b : MulAut W) w) = (b : MulAut W) ((a : MulAut W) w)
  rw [h1 a b w, h1 b a w]
  ac_rfl

end General

section Setting

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem insp5a_sec_Mp_le_stabSub (hD : D31 M Mp T L V) : Mp ≤ stabSub V := by
  have hinv := hD.irr.2.1
  exact le_stabSub_of_forall_mem fun x hx w hw => hinv ⟨x, hx⟩ w hw

omit [Finite W] in
theorem insp5a_sec_L_le_Mp (hD : D31 M Mp T L V) : L ≤ Mp := by
  rw [hD.Mp_eq]
  exact le_conjClosure L T

omit [Finite W] in
theorem insp5a_sec_T_le_normalizer (hD : D31 M Mp T L V) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [hD.Mp_eq]
  exact le_normalizer_conjClosure L T

omit [Finite W] in
theorem insp5a_sec_sup_le_normalizer (hD : D31 M Mp T L V) :
    Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
  sup_le Subgroup.le_normalizer (insp5a_sec_T_le_normalizer hD)

omit [Finite W] in
theorem insp5a_le_stabSub (hD : D31 M Mp T L V) : L ≤ stabSub V :=
  (insp5a_sec_L_le_Mp hD).trans (insp5a_sec_Mp_le_stabSub hD)

theorem insp5a_sec_exists_ne (hD : D31 M Mp T L V) (hcomm : commV L = V) :
    ∃ l ∈ L, ∃ v ∈ V, l v ≠ v :=
  insp5a_sec_exists_ne_of_commV_eq hcomm (not_isSolvable_of_mem_cComp hD.comp)

omit [Finite W] in
theorem insp5a_sec_isSimpleGroup (hL38 : A38Types ↥L) :
    IsSimpleGroup ↥L :=
  CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hL38

theorem insp5a_sec_isQuasisimple (hD : D31 M Mp T L V)
    (hL38 : A38Types ↥L) : CFSG.IsQuasisimple ↥L := by
  have := insp5a_sec_isSimpleGroup hL38
  have hns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_mem_cComp hD.comp
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hns (Group.isSolvable_of_comm h)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

theorem insp5a_faithful (hD : D31 M Mp T L V) (hcomm : commV L = V)
    (hL38 : A38Types ↥L) : L ⊓ centSub V = ⊥ := by
  have := insp5a_sec_isSimpleGroup hL38
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  obtain ⟨l₀, hl₀, v₀, hv₀, hne⟩ := insp5a_sec_exists_ne hD hcomm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resHomOn V hLs).ker with hk | hk
  · rw [eq_bot_iff]
    intro g hg
    have hmem : (⟨g, hg.1⟩ : ↥L) ∈ (resHomOn V hLs).ker := by
      rw [MonoidHom.mem_ker]
      ext u
      exact hg.2 u u.2
    rw [hk, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  · exfalso
    have hmem : (⟨l₀, hl₀⟩ : ↥L) ∈ (resHomOn V hLs).ker := by rw [hk]; trivial
    rw [MonoidHom.mem_ker] at hmem
    exact hne (congrArg (fun φ : MulAut ↥V => ((φ ⟨v₀, hv₀⟩ : ↥V) : W)) hmem)

theorem insp5a_exists_equiv (hD : D31 M Mp T L V) (hcomm : commV L = V)
    (hL38 : A38Types ↥L) :
    ∃ e : ↥L ≃* ↥(autSub L V),
      ∀ g : ↥L, ((e g : ↥(autSub L V)) : MulAut ↥V) = resHomOn V (insp5a_le_stabSub hD) g := by
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hfaith : L ⊓ centSub V = ⊥ := insp5a_faithful hD hcomm hL38
  have hinj : Function.Injective (resHomOn V hLs) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hc : (g : MulAut W) ∈ L ⊓ centSub V := by
      refine ⟨g.2, fun u hu => ?_⟩
      exact congrArg (fun φ : MulAut ↥V => ((φ ⟨u, hu⟩ : ↥V) : W)) hg
    rw [hfaith, Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.2 (Subtype.ext hc)
  exact ⟨(MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs).symm), fun g => rfl⟩

theorem insp5a_equiv (hD : D31 M Mp T L V) (hcomm : commV L = V)
    (hL38 : A38Types ↥L) : Nonempty (↥L ≃* ↥(autSub L V)) :=
  (insp5a_exists_equiv hD hcomm hL38).elim fun e _ => ⟨e⟩

omit [Finite W] in
theorem insp5a_sec_act (hD : D31 M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hN : (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ V, a u = l u := by
  intro a ha
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun g hg =>
    hN ⟨Subgroup.mem_sup_left hg, insp5a_sec_Mp_le_stabSub hD hg⟩
  have hLt : conjAutSub t L ≤ Mp := le_of_le_of_eq le_sup_right hMp.symm
  rw [hMp] at ha
  exact exists_mem_of_mem_sup_of_le_centSub (hLt.trans hMpN)
    (fun y hy u hu => hV0 u hu y hy) a ha

omit [Finite W] in
theorem insp5a_sec_commSub_eq (hD : D31 M Mp T L V) (hact : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ V, a u = l u) :
    commSub V L = V := by
  refine le_antisymm (commSub_le_of_invariant fun x hx w hw => ?_) ?_
  · exact (insp5a_le_stabSub hD hx w).2 hw
  · refine (hD.irr.2.2.1.symm.le).trans ?_
    rw [XMod.commOf_le_iff]
    intro a v hv
    obtain ⟨l, hl, hal⟩ := hact a a.2
    show (a : MulAut W) v * v⁻¹ ∈ commSub V L
    rw [hal v hv]
    exact Subgroup.subset_closure ⟨l, hl, v, hv, rfl⟩

omit [Finite W] in
theorem insp5a_sec_fixed_eq : XMod.fixed ↥Mp V = V ⊓ fixV Mp := by
  ext v
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun x hx => h ⟨x, hx⟩⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun a => h a a.2⟩

end Setting

section Fields

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
theorem insp5a_sec_normal {Y : Subgroup (MulAut W)}
    (hN : Y ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ x ∈ autSub Y V, ∀ k ∈ autSub L V, x * k * x⁻¹ ∈ autSub L V := by
  intro x hx k hk
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hk
  have hgN : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := hN ⟨hg, g.2⟩
  refine mem_autSub.mpr ⟨g * l * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hgN (l : MulAut W)).mp hl

omit [Finite W] in
theorem insp5a_sec_two (hD : D31 M Mp T L V) (hact : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ V, a u = l u)
    (hN : (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ x ∈ autSub (Mp ⊔ T) V, ∃ e : ℕ, x ^ 2 ^ e ∈ autSub L V := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  have hg' : (g : MulAut W) ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T (insp5a_sec_T_le_normalizer hD)] at hg'
  obtain ⟨m, hm, s, hs, hms⟩ := hg'
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hmV : m ∈ stabSub V := insp5a_sec_Mp_le_stabSub hD hm
  have hsV : s ∈ stabSub V := by
    have h1 : s = m⁻¹ * (g : MulAut W) := by rw [← hms]; group
    rw [h1]
    exact (stabSub V).mul_mem ((stabSub V).inv_mem hmV) g.2
  have hsX : resHom V ⟨s, hsV⟩ ∈ autSub (Mp ⊔ T) V :=
    mem_autSub.mpr ⟨⟨s, hsV⟩, Subgroup.mem_sup_right hs, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, s ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := (hD.sylow.2.1 : IsPGroup 2 ↥T) ⟨s, hs⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hσe : (resHom V ⟨s, hsV⟩) ^ 2 ^ e = 1 := by
    rw [← map_pow, show (⟨s, hsV⟩ : ↥(stabSub V)) ^ 2 ^ e = 1 from Subtype.ext (by simpa using he),
      map_one]
  have hσN : resHom V ⟨s, hsV⟩ ∈ Subgroup.normalizer ((autSub L V : Subgroup (MulAut ↥V)) :
      Set (MulAut ↥V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact insp5a_sec_normal hN _ hsX k hk
    · intro hk
      have h2 := insp5a_sec_normal hN _ ((autSub (Mp ⊔ T) V).inv_mem hsX) _ hk
      have e2 : (resHom V ⟨s, hsV⟩)⁻¹ * (resHom V ⟨s, hsV⟩ * k * (resHom V ⟨s, hsV⟩)⁻¹) *
          ((resHom V ⟨s, hsV⟩)⁻¹)⁻¹ = k := by group
      rw [e2] at h2
      exact h2
  have hκ : resHom V ⟨m, hmV⟩ ∈ autSub L V := by
    obtain ⟨l, hl, hal⟩ := hact m hm
    have : resHom V ⟨m, hmV⟩ = resHom V ⟨l, hLs hl⟩ := by
      ext u
      rw [resHom_apply, resHom_apply]
      exact hal u u.2
    rw [this]
    exact mem_autSub.mpr ⟨⟨l, hLs hl⟩, hl, rfl⟩
  have hgms : g = ⟨m, hmV⟩ * ⟨s, hsV⟩ := Subtype.ext hms.symm
  obtain ⟨k', hk', hpow⟩ := insp5a_sec_mul_pow_mem hκ hσN (2 ^ e)
  refine ⟨e, ?_⟩
  rw [hgms, map_mul, hpow, hσe, mul_one]
  exact hk'

omit [Finite W] in
theorem insp5a_sec_stab (hD : D31 M Mp T L V) :
    autSub (Mp ⊔ T) V ≤ stabSub ((V ⊓ fixV Mp).subgroupOf V) := by
  intro x hx u
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  have hgn : (g : MulAut W) ∈ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    insp5a_sec_sup_le_normalizer hD hg
  have key : ∀ y : MulAut W, y ∈ Subgroup.normalizer (Mp : Set (MulAut W)) →
      ∀ w : W, w ∈ fixV Mp → y w ∈ fixV Mp := by
    intro y hy w hw a ha
    have h1 : y⁻¹ * a * y ∈ Mp := (Subgroup.mem_normalizer_iff''.mp hy a).mp ha
    have h2 : y⁻¹ (a (y w)) = w := hw _ h1
    calc a (y w) = y (y⁻¹ (a (y w))) := by simp
      _ = y w := by rw [h2]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
  have hgV : (g : MulAut W) (u : W) ∈ V := (g.2 u).2 u.2
  constructor
  · rintro ⟨-, h⟩
    have h3 := key _ ((Subgroup.normalizer (Mp : Set (MulAut W))).inv_mem hgn) _ h
    exact ⟨u.2, by simpa using h3⟩
  · rintro ⟨-, h⟩
    exact ⟨hgV, key _ hgn _ h⟩

omit [Finite W] in
theorem insp5a_sec_fix (hD : D31 M Mp T L V) :
    (V ⊓ fixV Mp).subgroupOf V ≤ fixV (autSub L V) := by
  intro u hu φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  apply Subtype.ext
  rw [resHom_apply]
  exact (Subgroup.mem_subgroupOf.mp hu).2 _ (insp5a_sec_L_le_Mp hD hg)

omit [Finite W] in
theorem insp5a_sec_comm (hLs : L ≤ stabSub V) (hc : commSub V L = V) : commV (autSub L V) = ⊤ := by
  have h1 := map_commSub_autSub hLs (⊤ : Subgroup ↥V)
  have htop : (⊤ : Subgroup ↥V).map V.subtype = V := by
    rw [← MonoidHom.range_eq_map]
    exact V.range_subtype
  rw [htop, hc] at h1
  rw [commV_eq_commSub]
  apply Subgroup.map_injective V.subtype_injective
  rw [h1, htop]

omit [Finite W] in
theorem insp5a_sec_lt (hD : D31 M Mp T L V) : (V ⊓ fixV Mp).subgroupOf V < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have h' : V ≤ V ⊓ fixV Mp := Subgroup.subgroupOf_eq_top.mp h
  have hlt : XMod.fixed ↥Mp V < V := hD.irr.2.2.2.1
  apply hlt.not_ge
  intro v hv
  rw [insp5a_sec_fixed_eq]
  exact h' hv

omit [Finite W] in
theorem insp5a_sec_irr (hD : D31 M Mp T L V) (hact : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ V, a u = l u) :
    ∀ J : Subgroup ↥V, (V ⊓ fixV Mp).subgroupOf V ≤ J →
      (∀ k ∈ autSub L V, ∀ w ∈ J, k w ∈ J) →
      J = (V ⊓ fixV Mp).subgroupOf V ∨ J = ⊤ := by
  intro J hCJ hJ
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hinv : XMod.IsInv ↥Mp (J.map V.subtype) := by
    rintro ⟨a, ha⟩ _ ⟨w, hw, rfl⟩
    obtain ⟨l, hl, hal⟩ := hact a ha
    refine ⟨resHom V ⟨l, hLs hl⟩ w, hJ _ (mem_autSub.mpr ⟨⟨l, hLs hl⟩, hl, rfl⟩) w hw, ?_⟩
    rw [Subgroup.coe_subtype, resHom_apply]
    exact (hal w w.2).symm
  have hfix : XMod.fixed ↥Mp V ≤ J.map V.subtype := by
    rintro v ⟨hv, hfv⟩
    refine ⟨⟨v, hv⟩, hCJ ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hv, fun x hx => hfv ⟨x, hx⟩⟩
  rcases hD.irr.2.2.2.2 (J.map V.subtype) hinv hfix (Subgroup.map_subtype_le J) with h | h
  · left
    ext u
    have e1 : u ∈ J ↔ (u : W) ∈ J.map V.subtype :=
      (Subgroup.mem_map_iff_mem V.subtype_injective).symm
    rw [e1, h, insp5a_sec_fixed_eq, Subgroup.mem_subgroupOf]
  · right
    rw [eq_top_iff]
    intro u _
    have hu : (u : W) ∈ J.map V.subtype := by rw [h]; exact u.2
    exact (Subgroup.mem_map_iff_mem (x := u) V.subtype_injective).mp hu

end Fields

section Main

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem insp5a_qsec (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hcomm : commV L = V)
    (hL38 : A38Types ↥L)
    (hN : (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    InternalSec.QSec (autSub (Mp ⊔ T) V) (autSub L V) ((V ⊓ fixV Mp).subgroupOf V) := by
  have _ := htT
  have _ := htL
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hact := insp5a_sec_act hD hMp hV0 hN
  have hns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_mem_cComp hD.comp
  have hne : autSub L V ≠ ⊥ :=
    autSub_ne_bot_of_exists hLs le_rfl (insp5a_sec_exists_ne hD hcomm)
  have hle : autSub L V ≤ autSub (Mp ⊔ T) V :=
    autSub_mono ((insp5a_sec_L_le_Mp hD).trans le_sup_left) V
  have hstab := insp5a_sec_stab hD
  have hfix := insp5a_sec_fix hD
  have hsimple := insp5a_sec_isSimpleGroup hL38
  have hO2 : pCoreOf 2 (autSub L V) = ⊥ := pCoreOf_autSub_eq_bot_of_isSimple hLs hns hne
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.exp])
  obtain ⟨e⟩ := insp5a_equiv hD hcomm hL38
  exact
    { le := hle
      normal := insp5a_sec_normal hN
      two := insp5a_sec_two hD hact hN
      stab := hstab
      fix := hfix
      comm := insp5a_sec_comm hLs (insp5a_sec_commSub_eq hD hact)
      lt := insp5a_sec_lt hD
      irr := insp5a_sec_irr hD hact
      faithful := InternalSec.inf_centSec_eq_bot_of_pCoreOf hexp (hle.trans hstab) hfix hO2
      quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv e (insp5a_sec_isQuasisimple hD hL38) }

theorem insp5a_sqtk (hA21 : AsA21SQTKSection) (hD : D31 M Mp T L V)
    (hcomm : commV L = V) (hL38 : A38Types ↥L) : SQTKGroup ↥(autSub L V) := by
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hLq : CFSG.IsQuasisimple ↥L := insp5a_sec_isQuasisimple hD hL38
  obtain ⟨e⟩ := insp5a_equiv hD hcomm hL38
  have hq : CFSG.IsQuasisimple ↥(autSub L V) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hLq
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hD.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  have hSL : SQTKGroup ↥L :=
    B69.sqtk_subgroup hA21 hS φ hφ (le_of_mem_cComp hD.comp) hLq
  exact B69.sqtk_autSub hA21 hLs hSL hq

end Main

end CFSG.Quasithin
