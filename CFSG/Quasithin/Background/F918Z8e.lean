module

public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.F918Z8a
public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.LieType.BorelTits

section Perm

variable {W : Type} [CommGroup W] {M T L : Subgroup (MulAut W)} {t : MulAut W}

theorem d321e_conj_conj_inv (g : MulAut W) (X : Subgroup (MulAut W)) :
    conjAutSub g (conjAutSub g⁻¹ X) = X := by
  simpa using conjAutSub_inv_conjAutSub X g⁻¹

theorem d321e_perm_Lt
    (hperm : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L) (htM : t ∈ M)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) {m : MulAut W} (hm : m ∈ M)
    (hmL : conjAutSub m L = L) : conjAutSub m (conjAutSub t L) = conjAutSub t L := by
  rcases hperm (m * t) (M.mul_mem hm htM) with h | h
  · exfalso
    apply htL
    rw [d321a_conjAutSub_mul] at h
    exact d321a_mem_normalizer_iff.mpr (d321a_conjAutSub_inj (h.trans hmL.symm))
  · rwa [d321a_conjAutSub_mul] at h

theorem d321e_normal
    (hperm : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L) (htM : t ∈ M)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.normalizer (L : Set (MulAut W)) : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
  have key : ∀ g ∈ M, ∀ x ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      g * x * g⁻¹ ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro g hg x hx
    obtain ⟨hxM, hxN⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hg hxM) (M.inv_mem hg), ?_⟩
    rw [d321a_mem_normalizer_iff] at hxN ⊢
    have e : conjAutSub (g * x * g⁻¹) L = conjAutSub g (conjAutSub x (conjAutSub g⁻¹ L)) := by
      rw [d321a_conjAutSub_mul, d321a_conjAutSub_mul]
    rw [e]
    have hgg := d321e_conj_conj_inv g L
    rcases hperm g⁻¹ (M.inv_mem hg) with h | h
    · rw [h, hxN]
      rwa [h] at hgg
    · rw [h, d321e_perm_Lt hperm htM htL hxM hxN]
      rwa [h] at hgg
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have h1 := key g⁻¹ (M.inv_mem hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h1

theorem d321e_sylow [Finite W]
    (hperm : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L) (htM : t ∈ M)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hT : IsSylowTwoOf T M) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set (MulAut W)))
      (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) := by
  have h := A4.isSylowTwoOf_inf_normal hT
    (inf_le_left : M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ M)
    (d321e_normal hperm htM htL)
  have e : T ⊓ (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) =
      T ⊓ Subgroup.normalizer (L : Set (MulAut W)) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hT.1 h.1, h.2⟩⟩
  rwa [e] at h

end Perm

section Core

variable {W : Type} [CommGroup W] {M T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}

theorem d321e_V_le_commV (hVL : commSub V L = V) : V ≤ commV L := by
  calc V = commSub V L := hVL.symm
    _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
    _ = commV L := (commV_eq_commSub L).symm

theorem d321e_core
    (hgen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤) (hLM : L ≤ M) (htM : t ∈ M)
    (hperm : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hVL : commSub V L = V) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    commV L = ⨆ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map m.toMonoidHom := by
  have hmemP : ∀ g : MulAut W, g ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ↔
      g ∈ M ∧ conjAutSub g L = L := fun g => by
    rw [Subgroup.mem_inf, d321a_mem_normalizer_iff]
  have hti : conjAutSub t⁻¹ L = conjAutSub t L := by
    rcases hperm t⁻¹ (M.inv_mem htM) with h | h
    · exfalso
      apply htL
      have h1 : t⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        d321a_mem_normalizer_iff.mpr h
      simpa using (Subgroup.normalizer (L : Set (MulAut W))).inv_mem h1
    · exact h
  have hsplit : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub (t⁻¹ * g) L = L := by
    intro g hg
    rcases hperm g hg with h | h
    · exact Or.inl h
    · right
      rw [d321a_conjAutSub_mul, h, conjAutSub_inv_conjAutSub]
  set U₀ : Subgroup W := ⨆ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map m.toMonoidHom
    with hU0def
  have hU0mem : ∀ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), ∀ v ∈ V, m v ∈ U₀ := by
    intro m hm v hv
    have h1 : V.map m.toMonoidHom ≤ U₀ :=
      le_iSup₂ (f := fun (m : MulAut W) (_ : m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W))) =>
        V.map m.toMonoidHom) m hm
    exact h1 ⟨v, hv, rfl⟩
  have hU0le : ∀ C : Subgroup W,
      (∀ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), ∀ v ∈ V, m v ∈ C) → U₀ ≤ C := by
    intro C hC
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hC m hm v hv
  have hU0Lt : U₀ ≤ fixV (conjAutSub t L) := by
    refine hU0le _ fun m hm v hv x hx => ?_
    obtain ⟨hmM, hmL⟩ := (hmemP m).mp hm
    have hx' : m⁻¹ * x * m ∈ conjAutSub t L := by
      have : x ∈ conjAutSub m (conjAutSub t L) := by
        rw [d321e_perm_Lt hperm htM htL hmM hmL]
        exact hx
      exact mem_conjAutSub_iff.mp this
    have e : x (m v) = m ((m⁻¹ * x * m) v) := by simp [MulAut.mul_apply]
    rw [e, htriv v hv _ hx']
  have hVU : V ≤ commV L := d321e_V_le_commV hVL
  have hU0comm : U₀ ≤ commV L := by
    refine hU0le _ fun m hm v hv => ?_
    exact d321a_commV_stable (Subgroup.mem_inf.mp hm).2 (hVU hv)
  have hU0L : ∀ l ∈ L, ∀ u ∈ U₀, l u ∈ U₀ := by
    intro l hl u hu
    have hlP : l ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_inf.mpr ⟨hLM hl, Subgroup.le_normalizer hl⟩
    have h : U₀ ≤ U₀.comap l.toMonoidHom := by
      refine hU0le _ fun m hm v hv => ?_
      rw [Subgroup.mem_comap]
      exact hU0mem (l * m) ((M ⊓ Subgroup.normalizer (L : Set (MulAut W))).mul_mem hlP hm) v hv
    exact Subgroup.mem_comap.mp (h hu)
  have hgenle : (⊤ : Subgroup W) ≤ U₀ ⊔ U₀.map t.toMonoidHom := by
    refine hgen.symm.le.trans (iSup₂_le fun g hg => ?_)
    rintro _ ⟨v, hv, rfl⟩
    rcases hsplit g hg with h | h
    · exact Subgroup.mem_sup_left (hU0mem g ((hmemP g).mpr ⟨hg, h⟩) v hv)
    · refine Subgroup.mem_sup_right ⟨(t⁻¹ * g) v,
        hU0mem _ ((hmemP _).mpr ⟨M.mul_mem (M.inv_mem htM) hg, h⟩) v hv, ?_⟩
      simp [MulAut.mul_apply]
  have hbL : ∀ b ∈ U₀.map t.toMonoidHom, ∀ l ∈ L, l b = b := by
    rintro _ ⟨u, hu, rfl⟩ l hl
    have hy : t⁻¹ * l * t ∈ conjAutSub t L := by
      rw [← hti, mem_conjAutSub_iff]
      have e : t⁻¹⁻¹ * (t⁻¹ * l * t) * t⁻¹ = l := by group
      rw [e]
      exact hl
    have hfix : (t⁻¹ * l * t) u = u := hU0Lt hu _ hy
    show l (t u) = t u
    have e : l (t u) = t ((t⁻¹ * l * t) u) := by simp [MulAut.mul_apply]
    rw [e, hfix]
  have hUle : commV L ≤ U₀ := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hgenle (Subgroup.mem_top w))
    have e : l (a * b) * (a * b)⁻¹ = l a * a⁻¹ := by
      rw [map_mul, hbL b hb l hl, mul_inv_rev]
      group
    rw [e]
    exact U₀.mul_mem (hU0L l hl a ha) (U₀.inv_mem ha)
  exact le_antisymm hUle hU0comm

end Core

section Norm

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem d321e_Lt_le_normalizer (hcomm : ⁅L, conjAutSub t L⁆ = ⊥) :
    conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hLc : conjAutSub t L ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((Subgroup.commutator_comm _ _).trans hcomm)
  exact hLc.trans (Subgroup.centralizer_le_normalizer _)

theorem d321e_Mp_le_stab (hstd : D3Std M Mp T L V) : Mp ≤ stabSub V :=
  le_stabSub_of_forall_mem fun x hx w hw => hstd.hyp.irr.2.1 ⟨x, hx⟩ w hw

theorem d321e_T_le_normalizer (hstd : D3Std M Mp T L V) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [hstd.hyp.Mp_eq]
  exact le_normalizer_conjClosure L T

theorem d321e_Mp_le_stab_orbSup (hstd : D3Std M Mp T L V) : Mp ≤ stabSub (orbSup T V) := by
  refine le_stabSub_of_forall_mem fun x hx w hw => ?_
  have key : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    show x (s v) ∈ orbSup T V
    have hx' : s⁻¹ * x * s ∈ Mp :=
      (Subgroup.mem_normalizer_iff''.mp (d321e_T_le_normalizer hstd hs) x).mp hx
    have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
    rw [h1]
    exact map_le_orbSup hs ⟨_, (d321e_Mp_le_stab hstd hx' v).2 hv, rfl⟩
  exact key hw

theorem d321e_nontriv (hstd : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hLtN : conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  by_contra hcon
  push Not at hcon
  have h1 := hstd.hyp.irr.2.2.2.1
  have hfix : V ≤ XMod.fixed ↥Mp V := by
    intro v hv
    refine ⟨hv, fun a => ?_⟩
    have ha : (a : MulAut W) ∈ L ⊔ conjAutSub t L :=
      (congrArg (fun H : Subgroup (MulAut W) => (a : MulAut W) ∈ H) hMp).mp a.2
    obtain ⟨l, hl, hal⟩ := exists_mem_of_mem_sup_of_le_centSub (X := L) (Y := conjAutSub t L)
      (U := V) hLtN (fun y hy u hu => htriv u hu y hy) (a : MulAut W) ha
    show (a : MulAut W) v = v
    rw [hal v hv]
    exact hcon l hl v hv
  exact absurd hfix (not_le_of_gt h1)

omit [Finite W] in
theorem d321e_lt (htT : t ∈ T) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v) : V < orbSup T V := by
  refine lt_of_le_of_ne (le_orbSup T V) fun h => ?_
  obtain ⟨l, hl, v, hv, hne⟩ := hnt
  apply hne
  have htv : t v ∈ V := by
    have h1 : t v ∈ orbSup T V := mem_orbSup_of_mem_map htT (le_orbSup T V hv)
    rwa [← h] at h1
  have hmem : t * l * t⁻¹ ∈ conjAutSub t L := ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have h2 : t (l v) = t v := by simpa [MulAut.mul_apply] using htriv (t v) htv _ hmem
  exact t.injective h2

end Norm

section Decomp

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem d321e_t_not_stab {X : Subgroup W} (hVX : V ≤ X) (hcent : conjAutSub t L ≤ centSub X)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v) : t ∉ stabSub X := by
  intro ht
  obtain ⟨l, hl, v, hv, hne⟩ := hnt
  apply hne
  have hg : t * l * t⁻¹ ∈ conjAutSub t L := ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have h1 := mem_centSub.mp (hcent hg) (t v) ((mem_stabSub.mp ht v).2 (hVX hv))
  have h2 : t (l v) = t v := by simpa [MulAut.mul_apply] using h1
  exact t.injective h2

theorem d321e_T_stab_le (hL38 : D3L38) (n : D36Norm M Mp T L V t) {X : Subgroup W}
    (hS : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub X) (ht : t ∉ stabSub X) :
    ∀ s ∈ T, s ∈ stabSub X → s ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  intro s hsT hs
  rcases d36_split hL38 n s hsT with h | h
  · exact h
  · exfalso
    apply ht
    have hr : t⁻¹ * s ∈ stabSub X := hS ⟨T.mul_mem (T.inv_mem n.tT) hsT, h⟩
    have h' := (stabSub X).mul_mem hs ((stabSub X).inv_mem hr)
    rwa [show s * (t⁻¹ * s)⁻¹ = t by group] at h'

omit [Finite W] in
theorem d321e_decomp {X : Subgroup W} (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hMpX : Mp ≤ stabSub X) (hK1 : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ X, a u = l u)
    (hTX : ∀ s ∈ T, s ∈ stabSub X → s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    {g : MulAut W} (hg : g ∈ Mp ⊔ T) (hgX : g ∈ stabSub X) :
    ∃ l ∈ L, ∃ s ∈ T ⊓ Subgroup.normalizer (L : Set (MulAut W)), ∀ x ∈ X, g x = l (s x) := by
  have hg' : g ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T hTn] at hg'
  obtain ⟨m, hm, s', hs', hms⟩ := hg'
  have hmstab : m ∈ stabSub X := hMpX hm
  have hs'stab : s' ∈ stabSub X := by
    have h1 : s' = m⁻¹ * g := by rw [← hms]; group
    rw [h1]
    exact (stabSub X).mul_mem ((stabSub X).inv_mem hmstab) hgX
  obtain ⟨l, hl, hml⟩ := hK1 m hm
  refine ⟨l, hl, s', ⟨hs', hTX s' hs' hs'stab⟩, fun x hx => ?_⟩
  rw [← hms]
  show m (s' x) = l (s' x)
  exact hml _ ((mem_stabSub.mp hs'stab x).2 hx)

end Decomp

section CongrE

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

private noncomputable abbrev congrHomE : MulAut V →* MulAut V' := (MulAut.congr e).toMonoidHom

private theorem congrHomE_apply (x : MulAut V) (v : V') : congrHomE e x v = e (x (e.symm v)) :=
  rfl

private theorem congrHomE_symm_comp :
    (congrHomE e.symm).comp (congrHomE e) = MonoidHom.id (MulAut V) := by
  ext x v
  simp

private theorem kq_map_congr_leE [Finite V] [Finite V'] (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (congrHomE e)) k ≤ kq X k :=
  kq_map_mulAutCongr_le e X k

private theorem kq_le_of_leE [Finite V] {X G : Subgroup (MulAut V)} (h : G ≤ X) (k : ℕ) :
    kq X k ≤ kq G k := by
  rcases hx : kq G k with _ | r
  · exact le_top
  · have hr : kq G k ≤ (r : WithTop ℚ) := by rw [hx]; exact le_rfl
    obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp hr
    exact kq_le_iff.mpr ⟨A, ⟨hA.1.trans h, hA.2⟩, hAk, hAr⟩

end CongrE

section Transport

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem d321e_orbSup_subgroupOf {S : Subgroup (MulAut W)} {V U : Subgroup W} (hVU : V ≤ U)
    (hS : S ≤ stabSub U) :
    orbSup (autSub S U) (V.subgroupOf U) = (orbSup S V).subgroupOf U := by
  apply le_antisymm
  · refine orbSup_le fun τ hτ => ?_
    obtain ⟨⟨s, hsU⟩, hs, rfl⟩ := mem_autSub.mp hτ
    rintro _ ⟨x, hx, rfl⟩
    show ((resHom U ⟨s, hsU⟩ x : ↥U) : W) ∈ orbSup S V
    rw [resHom_apply]
    exact map_le_orbSup hs ⟨x, hx, rfl⟩
  · intro y hy
    have hle : orbSup S V ≤ (orbSup (autSub S U) (V.subgroupOf U)).map U.subtype := by
      refine orbSup_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      have hvU : v ∈ U := hVU hv
      refine ⟨resHom U ⟨s, hS hs⟩ ⟨v, hvU⟩, ?_, rfl⟩
      exact map_le_orbSup (mem_autSub.mpr ⟨⟨s, hS hs⟩, hs, rfl⟩) ⟨⟨v, hvU⟩, hv, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hle (Subgroup.mem_subgroupOf.mp hy)
    have : z = y := Subtype.ext hzy
    rwa [this] at hz

theorem d321e_qhat_transport {G L S : Subgroup (MulAut W)} {X U : Subgroup W} (hXU : X ≤ U)
    (hLU : L ≤ stabSub U) (hSU : S ≤ stabSub U) (hLX : L ≤ stabSub X) (hSX : S ≤ stabSub X)
    (hG : ∀ g ∈ G, g ∈ stabSub X → ∃ l ∈ L, ∃ s ∈ S, ∀ x ∈ X, g x = l (s x)) :
    qhatOf (autSub (autSub L U ⊔ autSub S U) (X.subgroupOf U)) ≤ qhatOf (autSub G X) := by
  have hsub : autSub G X ≤
      (autSub (autSub L U ⊔ autSub S U) (X.subgroupOf U)).map
        (congrHomE (Subgroup.subgroupOfEquivOfLe hXU)) := by
    intro φ hφ
    obtain ⟨⟨g, hgX⟩, hgG, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨l, hl, s, hs, hgls⟩ := hG g hgG hgX
    have hψv : ∀ x : ↥U,
        ((resHom U ⟨l, hLU hl⟩ * resHom U ⟨s, hSU hs⟩) x : W) = l (s x) := by
      intro x
      simp [MulAut.mul_apply, resHom_apply]
    have hψ : resHom U ⟨l, hLU hl⟩ * resHom U ⟨s, hSU hs⟩ ∈ autSub L U ⊔ autSub S U :=
      Subgroup.mul_mem_sup (mem_autSub.mpr ⟨⟨l, hLU hl⟩, hl, rfl⟩)
        (mem_autSub.mpr ⟨⟨s, hSU hs⟩, hs, rfl⟩)
    have hstab : resHom U ⟨l, hLU hl⟩ * resHom U ⟨s, hSU hs⟩ ∈ stabSub (X.subgroupOf U) := by
      refine mem_stabSub.mpr fun x => ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hψv]
      exact (mem_stabSub.mp (hLX hl) (s x)).trans (mem_stabSub.mp (hSX hs) x)
    refine ⟨resHom (X.subgroupOf U) ⟨_, hstab⟩, mem_autSub.mpr ⟨⟨_, hstab⟩, hψ, rfl⟩, ?_⟩
    ext v
    have e1 : ((Subgroup.subgroupOfEquivOfLe hXU).symm v : ↥(X.subgroupOf U)) =
        ⟨⟨v, hXU v.2⟩, v.2⟩ := rfl
    rw [congrHomE_apply, e1]
    show ((resHom (X.subgroupOf U) ⟨_, hstab⟩ ⟨⟨v, hXU v.2⟩, v.2⟩ : ↥(X.subgroupOf U)) :
      ↥U).1 = ((resHom X ⟨g, hgX⟩ v : ↥X) : W)
    rw [resHom_apply, resHom_apply]
    exact (hψv _).trans (hgls v v.2).symm
  have hback : (autSub G X).map (congrHomE (Subgroup.subgroupOfEquivOfLe hXU).symm) ≤
      autSub (autSub L U ⊔ autSub S U) (X.subgroupOf U) := by
    have h := Subgroup.map_mono (f := congrHomE (Subgroup.subgroupOfEquivOfLe hXU).symm) hsub
    rwa [Subgroup.map_map, congrHomE_symm_comp, Subgroup.map_id] at h
  exact (kq_le_of_leE hback 3).trans (kq_map_congr_leE _ _ 3)

end Transport

section Main

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d321e_perm (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L := by
  obtain ⟨hA38, hcomm, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hstd.hyp.quasi.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  exact fun g hg => d321a_perm hLs hnab hcomm hMp hstd.hyp.Mp_normal hg

theorem d3Std_restrict_U_gen (hL38 : D3L38)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hqS : qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    D3Std (autSub (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L))
      (autSub L (commV L))
      (autSub (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L))
      (autSub L (commV L)) (V.subgroupOf (commV L)) := by
  have hD := hstd.hyp
  obtain ⟨hA38, hcomm, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hLsimple : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hLtN := d321e_Lt_le_normalizer hcomm
  have hnt := d321e_nontriv hstd hMp htriv hLtN
  have n : D36Norm M Mp T L V t := ⟨hstd, d321e_lt htT htriv hnt, htT, htL, hMp, htriv⟩
  have hperm := d321e_perm hL38 hstd htT htL hMp
  have hTM : T ≤ M := hD.sylow.1
  have hLM : L ≤ M := le_of_mem_cComp hD.comp
  have hLMp : L ≤ Mp := by rw [hMp]; exact le_sup_left
  have hVL : commSub V L = V := d321_comm_eq hstd hMp htriv
  have hVU : V ≤ commV L := d321e_V_le_commV hVL
  have hUfix : commV L ≤ fixV (conjAutSub t L) := (d321_struct hL38 hstd htT htL hMp htriv).2
  have hUeq := d321e_core hD.gen hLM (hTM htT) hperm htL hVL htriv
  have hUTU : commSub (orbSup T V) L ≤ commV L :=
    (commSub_mono le_top le_rfl).trans (commV_eq_commSub L).ge
  have hVUT : V ≤ commSub (orbSup T V) L := d36_V_le_U hL38 n
  have hUTeq : commSub (orbSup T V) L = orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V :=
    d36_U_eq hL38 n
  have hLtcU : conjAutSub t L ≤ centSub (commV L) := fun y hy =>
    mem_centSub.mpr fun u hu => mem_fixV.mp (hUfix hu) y hy
  have hLtcUT : conjAutSub t L ≤ centSub (commSub (orbSup T V) L) := fun y hy =>
    mem_centSub.mpr fun u hu => mem_fixV.mp (hUfix (hUTU hu)) y hy
  have hLUT : L ≤ stabSub (commSub (orbSup T V) L) := fun _ hg =>
    mem_stabSub_commSub (d321e_Mp_le_stab_orbSup hstd (hLMp hg)) (Subgroup.le_normalizer hg)
  have hSUT : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commSub (orbSup T V) L) :=
    fun _ hg => mem_stabSub_commSub (le_stabSub_orbSup T V hg.1) hg.2
  have hMpUT : Mp ≤ stabSub (commSub (orbSup T V) L) := by
    rw [hMp]
    exact sup_le hLUT (hLtcUT.trans (centSub_le_stabSub _))
  have hK1UT : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ commSub (orbSup T V) L, a u = l u := by
    intro a ha
    rw [hMp] at ha
    exact exists_mem_of_mem_sup_of_le_centSub hLtN hLtcUT a ha
  have htUT : t ∉ stabSub (commSub (orbSup T V) L) := d321e_t_not_stab hVUT hLtcUT hnt
  have hG : ∀ g ∈ Mp ⊔ T, g ∈ stabSub (commSub (orbSup T V) L) → ∃ l ∈ L,
      ∃ s ∈ T ⊓ Subgroup.normalizer (L : Set (MulAut W)),
        ∀ x ∈ commSub (orbSup T V) L, g x = l (s x) := fun g hg hgX =>
    d321e_decomp (d321e_T_le_normalizer hstd) hMpUT hK1UT
      (d321e_T_stab_le hL38 n hSUT htUT) hg hgX
  set U := commV L with hUdef
  set ML := M ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hML
  set S := T ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hS
  have hSML : S ≤ ML := fun x hx => ⟨hTM hx.1, hx.2⟩
  have hLML : L ≤ ML := fun x hx => ⟨hLM hx, Subgroup.le_normalizer hx⟩
  have hMLM : ML ≤ M := inf_le_left
  have hMLL : ML ≤ Subgroup.normalizer (L : Set (MulAut W)) := inf_le_right
  have hSL : S ≤ Subgroup.normalizer (L : Set (MulAut W)) := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hMLs : ML ≤ stabSub U := d321a_le_stabSub_of_inv fun x hx w hw =>
    d321a_commV_stable (Subgroup.mem_inf.mp hx).2 hw
  have hLs : L ≤ stabSub U := hLML.trans hMLs
  have hSs : S ≤ stabSub U := hSML.trans hMLs
  have hK1 : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ U, a u = l u := by
    intro a ha
    rw [hMp] at ha
    exact exists_mem_of_mem_sup_of_le_centSub hLtN hLtcU a ha
  have hMps : Mp ≤ stabSub U := d321a_le_stabSub_of_inv fun a ha u hu => by
    obtain ⟨l, hl, hal⟩ := hK1 a ha
    rw [hal u hu]
    exact (mem_stabSub.mp (hLs hl) u).2 hu
  have horb : orbSup (autSub S U) (V.subgroupOf U) = (commSub (orbSup T V) L).subgroupOf U := by
    rw [d321e_orbSup_subgroupOf hVU hSs, ← hUTeq]
  have hexp : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.exp])
  have eL : autSub L U = (L.subgroupOf ML).map (resHomOn U hMLs) :=
    autSub_eq_map_resHomOn hLML hMLs
  have eS : autSub S U = (S.subgroupOf ML).map (resHomOn U hMLs) :=
    autSub_eq_map_resHomOn hSML hMLs
  have eX : autSub ML U = (ML.subgroupOf ML).map (resHomOn U hMLs) :=
    autSub_eq_map_resHomOn le_rfl hMLs
  have hLne : autSub L U ≠ ⊥ := autSub_ne_bot_of_exists hLs hVU hnt
  have hSyl : IsSylowTwoOf S ML := d321e_sylow hperm (hTM htT) htL hD.sylow
  have hMnorm : autSub ML U ≤ Subgroup.normalizer (autSub L U : Set (MulAut ↥U)) := by
    rw [eX, eL]
    exact map_le_normalizer_map_of_le_normalizer (resHomOn U hMLs) hLML hMLL
  have hSylF : IsSylowTwoOf (autSub S U) (autSub ML U) := by
    rw [eS, eX]
    exact isSylowTwoOf_map_subgroupOf (resHomOn U hMLs) hSyl
  have hcomp : autSub L U ∈ cComp (autSub ML U) := by
    rw [eL, eX]
    exact map_subgroupOf_mem_cComp (resHomOn U hMLs) (cComp_mem_of_le hD.comp hLML hMLM)
      (by rw [← eL]; exact hLne)
  have hquasi : CFSG.IsQuasisimple ↥(autSub L U) := by
    rw [eL]
    exact isQuasisimple_map_subgroupOf_of_ne_bot hLML hD.quasi (resHomOn U hMLs)
      (by rw [← eL]; exact hLne)
  have hcc : conjClosure L S = L := le_antisymm
    (conjClosure_le fun s hs z hz => (Subgroup.mem_normalizer_iff.mp (hSL hs) z).mp hz)
    (le_conjClosure L S)
  have hMpeq : autSub L U = conjClosure (autSub L U) (autSub S U) := by
    have h := map_subgroupOf_conjClosure (resHomOn U hMLs) hLML hSML
    rw [hcc] at h
    rw [eL, eS]
    exact h
  have hMpAC : ActCompat U.subtype (autSub L U) Mp := actCompat_autSub hMps hLMp hK1
  have hSAC : ActCompat U.subtype (autSub S U) S :=
    actCompat_autSub hSs le_rfl (fun a ha => ⟨a, ha, fun u _ => rfl⟩)
  have hmapV : (V.subgroupOf U).map U.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVU
  have hVirr : XMod.IsIrrPlus ↥(autSub L U) (V.subgroupOf U) :=
    (hMpAC.isIrrPlus_map_iff U.subtype_injective (V.subgroupOf U)).mp
      (by rw [hmapV]; exact hD.irr.2)
  have hTn := d321e_T_le_normalizer hstd
  have hSMp : S ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hST.trans hTn
  have hWT : ∀ s ∈ T, ∀ w ∈ orbSup T V, s • w ∈ orbSup T V := fun s hs w hw =>
    mem_orbSup_of_mem_map hs hw
  have hI : V ∈ IrrPlus Mp (orbSup T V) := hstd.irrT.1
  have hirrS : V ∈ IrrPlusOn Mp (orbSup T V) S := by
    refine (forall_smul_eq_iff_mem_irrPlusOn hSMp (fun s hs w hw => hWT s (hST hs) w hw) hI).mp ?_
    intro s hs
    exact ((forall_smul_eq_iff_mem_irrPlusOn hTn hWT hI).mpr hstd.irrT) s ⟨hST hs.1, hs.2⟩
  have hTnAut : autSub S U ≤ Subgroup.normalizer (autSub L U : Set (MulAut ↥U)) :=
    (autSub_mono hSML U).trans hMnorm
  have hirrT : V.subgroupOf U ∈
      IrrPlusOn (autSub L U) (orbSup (autSub S U) (V.subgroupOf U)) (autSub S U) := by
    rw [orbSup_eq_biSup_smul]
    exact hMpAC.mem_irrPlusOn_of_map U.subtype_injective hSAC hTnAut hSMp
      (Wq := orbSup T V) (fun s hs w hw => hWT s (hST hs) w hw) (by rw [hmapV]; exact hirrS)
  have hSylF' : IsSylowTwoOf (autSub S U) (autSub L U ⊔ autSub S U) :=
    isSylowTwoOf_mono_right hSylF le_sup_right
      (sup_le (autSub_mono hLML U) (autSub_mono hSML U))
  have hO2 : pCoreOf 2 (autSub L U) = ⊥ :=
    pCoreOf_autSub_eq_bot_of_isSimple hLs (not_isSolvable_of_mem_cComp hD.comp) hLne
  have ho2 := o2inv_of_irrPlusOn hTnAut hSylF' hO2 hirrT
  have hgen : (⨆ m ∈ autSub ML U, (V.subgroupOf U).map m.toMonoidHom) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : W) ∈ ⨆ m ∈ ML, V.map m.toMonoidHom := by
      rw [← hUeq]
      exact x.2
    have hle : (⨆ m ∈ ML, V.map m.toMonoidHom) ≤
        (⨆ m ∈ autSub ML U, (V.subgroupOf U).map m.toMonoidHom).map U.subtype := by
      refine iSup₂_le fun m hm => ?_
      rintro _ ⟨v, hv, rfl⟩
      have hvU : v ∈ U := hVU hv
      refine ⟨resHom U ⟨m, hMLs hm⟩ ⟨v, hvU⟩, ?_, rfl⟩
      have h1 : (V.subgroupOf U).map (resHom U ⟨m, hMLs hm⟩).toMonoidHom ≤
          ⨆ m ∈ autSub ML U, (V.subgroupOf U).map m.toMonoidHom :=
        le_iSup₂ (f := fun (m : MulAut ↥U) (_ : m ∈ autSub ML U) =>
          (V.subgroupOf U).map m.toMonoidHom) _
          (mem_autSub.mpr ⟨⟨m, hMLs hm⟩, hm, rfl⟩)
      exact h1 ⟨⟨v, hvU⟩, hv, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle hx
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hqhat : qhatOf (autSub (autSub L U ⊔ autSub S U)
      (orbSup (autSub S U) (V.subgroupOf U))) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [qhatOf_autSub_congr horb]
    exact (d321e_qhat_transport hUTU hLs hSs hLUT hSUT hG).trans hqS
  exact ⟨⟨hexp, isQuotientOfSQTK_autSub_aux hMLM hD.qsqtk, hSylF, hcomp, hquasi, hMpeq, hMnorm,
    ⟨le_top, hVirr⟩, ho2, hgen⟩, hqhat, hirrT⟩

theorem d3Std_restrict_U (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hlt : V < orbSup T V) (hVT : commSub (orbSup T V) L = V)
    (hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ)) :
    D3Std (autSub (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L))
      (autSub L (commV L))
      (autSub (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L))
      (autSub L (commV L)) (V.subgroupOf (commV L)) := by
  have _ := hlt
  exact d3Std_restrict_U_gen hL38 hstd htT htL hMp htriv
    ((qhatOf_autSub_congr hVT).trans_le hqV)

end Main

end CFSG.Quasithin
