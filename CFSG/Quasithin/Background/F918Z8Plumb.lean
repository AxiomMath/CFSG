module

public import CFSG.Quasithin.Background.F918Z8Def3
public import CFSG.Quasithin.Background.F918Z8d
public import CFSG.Quasithin.Background.F918Z8e
public import CFSG.Quasithin.Background.F918Z8f
public import CFSG.Quasithin.Background.F918Z8g
public import CFSG.Quasithin.Background.F918Z8h

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Basic

variable {W : Type} [CommGroup W]

theorem d321p_normalizer_le_stabSub_commV (L : Subgroup (MulAut W)) :
    Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commV L) :=
  d321a_le_stabSub_of_inv fun _ hx _ hw => d321a_commV_stable hx hw

theorem d321p_normalizer_le_stabSub_fixV (P : Subgroup (MulAut W)) :
    Subgroup.normalizer (P : Set (MulAut W)) ≤ stabSub (fixV P) := fun _ hg =>
  mem_stabSub_fixV (fun p hp => (Subgroup.mem_normalizer_iff.mp hg p).mp hp)
    (fun p hp => (Subgroup.mem_normalizer_iff''.mp hg p).mp hp)

theorem d321p_le_stabSub_inf {X : Subgroup (MulAut W)} {A B : Subgroup W} (hA : X ≤ stabSub A)
    (hB : X ≤ stabSub B) : X ≤ stabSub (A ⊓ B) := fun g hg u => by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA hg u, hB hg u]

theorem d321p_le_fixV_of_comm_le {L : Subgroup (MulAut W)} (hL : Group.IsPerfect ↥L)
    {X Y : Subgroup W} (hY : Y ≤ fixV L) (h : ∀ l ∈ L, ∀ x ∈ X, l x * x⁻¹ ∈ Y) :
    X ≤ fixV L := by
  intro x hx l hl
  let f : ↥L →* W :=
    { toFun := fun a => (a : MulAut W) x * x⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hy : (b : MulAut W) x * x⁻¹ ∈ fixV L := hY (h b b.2 x hx)
        have hya : (a : MulAut W) ((b : MulAut W) x * x⁻¹) = (b : MulAut W) x * x⁻¹ := hy a a.2
        have e : (a : MulAut W) ((b : MulAut W) x) =
            (a : MulAut W) ((b : MulAut W) x * x⁻¹) * (a : MulAut W) x := by
          rw [← map_mul, inv_mul_cancel_right]
        show (a : MulAut W) ((b : MulAut W) x) * x⁻¹ =
          ((a : MulAut W) x * x⁻¹) * ((b : MulAut W) x * x⁻¹)
        rw [e, hya]
        ac_rfl }
  have hmem : (⟨l, hl⟩ : ↥L) ∈ commutator ↥L := by
    rw [hL.commutator_eq_top]
    exact Subgroup.mem_top _
  have h1 := Abelianization.commutator_subset_ker f hmem
  rw [MonoidHom.mem_ker] at h1
  exact mul_inv_eq_one.mp h1

end Basic

section Quot

variable {G : Type*} [CommGroup G]

theorem d321p_quotHom_stab_map {N X : Subgroup G} (g : stabSub N)
    (hgX : (g : MulAut G) ∈ stabSub X) :
    quotHom N g ∈ stabSub (X.map (QuotientGroup.mk' N)) := by
  rw [mem_stabSub_iff_map_eq] at hgX ⊢
  have hcomp : (quotHom N g).toMonoidHom.comp (QuotientGroup.mk' N) =
      (QuotientGroup.mk' N).comp (g : MulAut G).toMonoidHom := by
    ext v
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hgX]

end Quot

section Std

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem d321p_le_Mp (hMp : Mp = L ⊔ conjAutSub t L) : L ≤ Mp := by
  rw [hMp]
  exact le_sup_left

theorem d321p_L_le_ML (hstd : D3Std M Mp T L V) :
    L ≤ M ⊓ Subgroup.normalizer (L : Set (MulAut W)) :=
  le_inf (le_of_mem_cComp hstd.hyp.comp) Subgroup.le_normalizer

omit [Finite W] in
theorem d321p_ML_stab_U (M L : Subgroup (MulAut W)) :
    M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commV L) :=
  inf_le_right.trans (d321p_normalizer_le_stabSub_commV L)

theorem d321p_ML_stab_Z (hstd : D3Std M Mp T L V) :
    M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commV L ⊓ fixV Mp) :=
  d321p_le_stabSub_inf (d321p_ML_stab_U M L)
    ((inf_le_left.trans hstd.hyp.Mp_normal).trans (d321p_normalizer_le_stabSub_fixV Mp))

theorem d321p_L_stab_U (hstd : D3Std M Mp T L V) : L ≤ stabSub (commV L) :=
  (d321p_L_le_ML hstd).trans (d321p_ML_stab_U M L)

theorem d321p_L_stab_Z (hstd : D3Std M Mp T L V) : L ≤ stabSub (commV L ⊓ fixV Mp) :=
  (d321p_L_le_ML hstd).trans (d321p_ML_stab_Z hstd)

omit [Finite W] in
theorem d321p_fix (hMp : Mp = L ⊔ conjAutSub t L) :
    (commV L ⊓ fixV Mp).subgroupOf (commV L) ≤ fixV (autSub L (commV L)) := fun _ hz =>
  mem_fixV_autSub.mpr fun g hg _ => ((Subgroup.mem_subgroupOf.mp hz).2) g (d321p_le_Mp hMp hg)

theorem d321p_stab (hstd : D3Std M Mp T L V) :
    autSub (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L) ≤
      stabSub ((commV L ⊓ fixV Mp).subgroupOf (commV L)) :=
  autSub_le_stabSub_subgroupOf (d321p_ML_stab_Z hstd)

theorem d321p_VS (hL38 : D3L38) (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hVT : commSub (orbSup T V) L = V) :
    V.subgroupOf (commV L) = orbSup (autSub (T ⊓ Subgroup.normalizer (L : Set (MulAut W)))
      (commV L)) (V.subgroupOf (commV L)) :=
  (orbSup_eq_of_stab fun _ hφ => autSub_le_stabSub_subgroupOf
    (d321_stab_V hL38 hstd htT htL hMp hVT) hφ).symm

theorem d321p_V_ne_bot (hstd : D3Std M Mp T L V) : V ≠ ⊥ := by
  intro h
  have h1 := hstd.hyp.irr.2.2.2.1
  rw [h] at h1
  exact not_lt_bot h1

theorem d321p_V_le_commV (hstd : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) : V ≤ commV L :=
  calc V = commSub V L := (d321_comm_eq hstd hMp htriv).symm
    _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
    _ = commV L := (commV_eq_commSub L).symm

theorem d321_faithful_tilde (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    L ⊓ centSec (commV L) (commV L ⊓ fixV Mp) = ⊥ := by
  obtain ⟨hA38, -, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hLU := d321p_L_stab_U hstd
  have hLZ := d321p_L_stab_Z hstd
  rcases hLs.eq_bot_or_eq_top_of_normal (d321f_secHom hLU hLZ).ker with h | h
  · refine eq_bot_iff.2 fun g hg => ?_
    have h1 : (⟨g, hg.1⟩ : ↥L) ∈ (d321f_secHom hLU hLZ).ker :=
      (d321f_mem_ker_secHom hLU hLZ ⟨g, hg.1⟩).2 hg.2
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  · exfalso
    have hall : ∀ l ∈ L, ∀ u ∈ commV L, l u * u⁻¹ ∈ commV L ⊓ fixV Mp := by
      intro l hl u hu
      have h1 : (⟨l, hl⟩ : ↥L) ∈ (d321f_secHom hLU hLZ).ker := by
        rw [h]
        exact Subgroup.mem_top _
      exact ((d321f_mem_ker_secHom hLU hLZ ⟨l, hl⟩).1 h1).2 u hu
    have hperf : Group.IsPerfect ↥L := hstd.hyp.quasi.1
    have hZL : commV L ⊓ fixV Mp ≤ fixV L := fun z hz l hl => hz.2 l (d321p_le_Mp hMp hl)
    have h1 : commV L ≤ fixV L := d321p_le_fixV_of_comm_le hperf hZL hall
    have h2 : (⊤ : Subgroup W) ≤ fixV L :=
      d321p_le_fixV_of_comm_le hperf h1 fun l hl w _ => Subgroup.subset_closure ⟨l, hl, w, rfl⟩
    have h3 : commV L = ⊥ := by
      rw [commV_eq_commSub]
      exact commSub_eq_bot_iff.2 h2
    exact d321p_V_ne_bot hstd (le_bot_iff.1 (h3 ▸ d321p_V_le_commV hstd hMp htriv))

theorem d321_stab_tilde (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hVT : commSub (orbSup T V) L = V) :
    autSec (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L) (commV L ⊓ fixV Mp) ≤
      stabSub (tildeImg (commV L) (commV L ⊓ fixV Mp) V) := by
  have _ := htriv
  intro φ hφ
  obtain ⟨g', hg', rfl⟩ := mem_autQuot.mp hφ
  exact d321p_quotHom_stab_map g'
    (autSub_le_stabSub_subgroupOf (d321_stab_V hL38 hstd htT htL hMp hVT) hg')

theorem d321_hK_tilde (hL38 : D3L38) (hOp : D321OpPrimeC)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    ∀ g ∈ autSec (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L) (commV L ⊓ fixV Mp),
      (∀ x ∈ autSec L (commV L) (commV L ⊓ fixV Mp), g * x = x * g) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥(autSec L (commV L) (commV L ⊓ fixV Mp)) →
      (∃ k : ℕ, g ^ (p ^ k) = 1) → g = 1 := by
  intro g hg hcomm p hp hp2 hpd hk
  obtain ⟨k, hk⟩ := hk
  have hf := d321_faithful_tilde hL38 hstd htT htL hMp htriv
  have hLML := d321p_L_le_ML hstd
  have hMLU := d321p_ML_stab_U M L
  have hMLZ := d321p_ML_stab_Z hstd
  have hLU := d321p_L_stab_U hstd
  have hLZ := d321p_L_stab_Z hstd
  obtain ⟨ĝ, rfl⟩ : g ∈ (d321f_secHom hMLU hMLZ).range := by
    rw [d321f_range_secHom]
    exact hg
  have hcent : ∀ x ∈ L, (ĝ : MulAut W) * x = x * (ĝ : MulAut W) := by
    intro x hx
    have h1 : d321f_secHom hMLU hMLZ ⟨x, hLML hx⟩ ∈ autSec L (commV L) (commV L ⊓ fixV Mp) := by
      rw [← d321f_range_secHom hLU hLZ]
      exact ⟨⟨x, hx⟩, rfl⟩
    have h2 := hcomm _ h1
    have h3 : d321f_secHom hMLU hMLZ (ĝ * ⟨x, hLML hx⟩ * ĝ⁻¹ * ⟨x, hLML hx⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h2]
      group
    have h4 : (ĝ : MulAut W) * x * (ĝ : MulAut W)⁻¹ * x⁻¹ ∈
        L ⊓ centSec (commV L) (commV L ⊓ fixV Mp) := by
      refine ⟨?_, (d321f_mem_ker_secHom hMLU hMLZ _).1 h3⟩
      have hĝN : (ĝ : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.mem_inf.mp ĝ.2).2
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hĝN x).mp hx) (L.inv_mem hx)
    rw [hf, Subgroup.mem_bot] at h4
    calc (ĝ : MulAut W) * x
        = ((ĝ : MulAut W) * x * (ĝ : MulAut W)⁻¹ * x⁻¹) * (x * (ĝ : MulAut W)) := by group
      _ = x * (ĝ : MulAut W) := by rw [h4, one_mul]
  have hpL : p ∣ Nat.card ↥L := by
    rw [Nat.card_congr (d321f_autSecEquiv hLU hLZ hf).toEquiv]
    exact hpd
  obtain ⟨a, m', hm', hmm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (ĝ : MulAut W)).ne' p hp.ne_one
  have hĝM : (ĝ : MulAut W) ^ m' ∈ M := M.pow_mem (Subgroup.mem_inf.mp ĝ.2).1 m'
  have hcent' : ∀ x ∈ L, (ĝ : MulAut W) ^ m' * x = x * (ĝ : MulAut W) ^ m' := fun x hx =>
    Commute.pow_left (hcent x hx) m'
  have hpow : ((ĝ : MulAut W) ^ m') ^ (p ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hmm]
    exact pow_orderOf_eq_one _
  have hfix := hOp W M Mp T L V t hstd htT htL hMp htriv _ hĝM hcent' p hp hp2 hpL ⟨a, hpow⟩
  have h5 : d321f_secHom hMLU hMLZ (ĝ ^ m') = 1 := by
    rw [← MonoidHom.mem_ker, d321f_mem_ker_secHom]
    refine ⟨hMLU (ĝ ^ m').2, fun w hw => ?_⟩
    rw [Subgroup.coe_pow, hfix w hw, mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [map_pow] at h5
  have hcop : Nat.Coprime (p ^ k) m' :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm')
  have h6 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h5)
  rw [Nat.Coprime.gcd_eq_one hcop] at h6
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h6)

end Std

section Assembly

variable {W : Type} [CommGroup W] [Finite W]

theorem d321Core_of_local (hL38 : D3L38) (hLoc : D321Local)
    (hOp : D321OpPrimeC) (hEx : D321Exact) : D321Core := by
  intro W _ _ M Mp T L V t A hstd htT htL hMp hqM hA htriv hlt hVT hqV htop
  have hD1 := d3Std_restrict_U hL38 hstd htT htL hMp htriv hlt hVT hqV
  have hD2 := d3Std_quot hD1 (d321p_VS hL38 hstd htT htL hMp hVT) (d321p_fix hMp)
    (d321p_stab hstd)
  have hf := d321_faithful_tilde hL38 hstd htT htL hMp htriv
  have hLU := d321p_L_stab_U hstd
  have hLZ := d321p_L_stab_Z hstd
  have hZU : commV L ⊓ fixV Mp ≤ commV L := inf_le_left
  have hcfg : LocCfg (autSec (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L)
      (commV L ⊓ fixV Mp)) (autSec L (commV L) (commV L ⊓ fixV Mp))
      (autSec (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L) (commV L ⊓ fixV Mp))
      (tildeImg (commV L) (commV L ⊓ fixV Mp) V) :=
    { std := hD2
      hq := d321_qhat_restrict hL38 hstd htT htL hMp hA htriv
      VS := by
        rw [orbSup_eq_of_stab fun s hs => d321_stab_tilde hL38 hstd htT htL hMp htriv hVT hs]
      ne := d321_tilde_ne_top hL38 hstd htT htL hMp htriv hVT htop
      fix := d321_fix_tilde hL38 hstd htT htL hMp htriv
      a38 := a38Types_congr (d321f_autSecEquiv hLU hLZ hf)
        (hL38 W M Mp T L V hstd t htT htL hMp).1
      hK := d321_hK_tilde hL38 hOp hstd htT htL hMp htriv }
  rcases hLoc _ _ _ _ _ hcfg with ⟨hpsl, hds⟩ | ⟨n, hpsl, K, hKf, hKfin, hcard, hds⟩
  · left
    have hpsl' := d321f_isPSL_of_autSec hLU hLZ hf hpsl
    have h4 := d321f_directSum_of_autSec hLU hLZ hZU hf hds
    have hZbot := hEx W M Mp T L V t A hstd htT htL hMp hqM hA htriv hlt hVT hqV htop hpsl' h4
    refine ⟨hpsl', ?_⟩
    rw [hZbot] at h4
    exact h4
  · right
    exact ⟨n, d321f_isPSL_of_autSec hLU hLZ hf hpsl, K, hKf, hKfin, hcard,
      d321f_directSum_of_autSec hLU hLZ hZU hf hds⟩

end Assembly

end CFSG.Quasithin
