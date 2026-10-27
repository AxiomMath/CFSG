module

public import CFSG.Quasithin.EmptyFaithful.S146zRHat
public import CFSG.Quasithin.EmptyFaithful.S146zRL3Case
public import CFSG.Quasithin.EmptyFaithful.S146zRL3B
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.Quasithin.Background.GoldschmidtS146PGroups

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section Normalizers

variable {X : Type*} [Group X]

theorem q_mem_normalizer_inf {A B : Subgroup X} {z : X}
    (hA : z ∈ Subgroup.normalizer (A : Set X)) (hB : z ∈ Subgroup.normalizer (B : Set X)) :
    z ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA y, hB y]

theorem q_mem_normalizer_sup {A B : Subgroup X} {z : X}
    (hA : z ∈ Subgroup.normalizer (A : Set X)) (hB : z ∈ Subgroup.normalizer (B : Set X)) :
    z ∈ Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

end Normalizers

section Odd

variable {X : Type} [Group X] [Finite X] {N₁ N₂ : Subgroup X} {ŝ : X}

omit [Finite X] in
theorem q_pow_eq_one_of_prod (hF : CaseIFacts N₁ N₂ ŝ) {a b : X} (ha : a ∈ N₁) (hb : b ∈ N₂) {r : ℕ}
    (h : (a * b) ^ r = 1) : a ^ r = 1 ∧ b ^ r = 1 := by
  have hc : Commute a b := hF.comm a ha b hb
  rw [hc.mul_pow] at h
  have h1 : a ^ r ∈ N₁ ⊓ N₂ := by
    refine ⟨N₁.pow_mem ha r, ?_⟩
    have : a ^ r = (b ^ r)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact N₂.inv_mem (N₂.pow_mem hb r)
  rw [hF.disj, Subgroup.mem_bot] at h1
  refine ⟨h1, ?_⟩
  rw [h1, one_mul] at h
  exact h

omit [Finite X] in
theorem q_exists_odd_mem_inf (hF : CaseIFacts N₁ N₂ ŝ) {Kh : Subgroup X} (hK : Kh ≤ N₁ ⊔ N₂)
    (hŝ : ŝ⁻¹ ∈ Subgroup.normalizer (Kh : Set X)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {k : X}
    (hk : k ∈ Kh) (hk1 : k ≠ 1) (hkr : orderOf k = r) :
    ∃ y ∈ N₁ ⊓ (Kh ⊔ N₂), y ≠ 1 ∧ Odd (orderOf y) := by
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have hkr1 : k ^ r = 1 := by rw [← hkr]; exact pow_orderOf_eq_one k
  have hmul : (↑(N₁ ⊔ N₂) : Set X) = ↑N₁ * ↑N₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ (q_normalizes_of_comm hF.comm)
  have hk' : k ∈ (↑(N₁ ⊔ N₂) : Set X) := hK hk
  rw [hmul] at hk'
  obtain ⟨a, ha, b, hb, rfl⟩ := hk'
  obtain ⟨har, hbr⟩ := q_pow_eq_one_of_prod hF ha hb hkr1
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hk1 (by simp [h])
    have hbN : ŝ⁻¹ * b * ŝ ∈ N₁ := by
      have : b ∈ N₁.map (MulAut.conj ŝ).toMonoidHom := hF.conj ▸ hb
      exact QWr.mem_map_conj.mp this
    have hbK : ŝ⁻¹ * b * ŝ ∈ Kh := by
      have hbK0 : b ∈ Kh := by simpa using hk
      have := (Subgroup.mem_normalizer_iff.mp hŝ b).mp hbK0
      simpa using this
    refine ⟨ŝ⁻¹ * b * ŝ, ⟨hbN, Subgroup.mem_sup_left hbK⟩, ?_, ?_⟩
    · intro h
      apply hb1
      have : ŝ * (ŝ⁻¹ * b * ŝ) * ŝ⁻¹ = b := by group
      rw [← this, h]
      group
    · have hord : orderOf (ŝ⁻¹ * b * ŝ) = orderOf b := by
        have : ŝ⁻¹ * b * ŝ = MulAut.conj ŝ⁻¹ b := by simp
        rw [this, MulEquiv.orderOf_eq]
      have hbo : orderOf b = r := by simpa using hkr
      rw [hord, hbo]
      exact hodd
  · refine ⟨a, ⟨ha, ?_⟩, ha1, ?_⟩
    · have : a = a * b * b⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (N₂.inv_mem hb))
    · have hdvd : orderOf a ∣ r := orderOf_dvd_of_pow_eq_one har
      have : orderOf a = r :=
        ((Nat.dvd_prime hr).mp hdvd).resolve_left (fun h => ha1 (orderOf_eq_one_iff.mp h))
      rw [this]
      exact hodd

theorem q_not_dvd_card_Y (hF : CaseIFacts N₁ N₂ ŝ) {Kh : Subgroup X} (hK : Kh ≤ N₁ ⊔ N₂) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hKℓ : ¬ ℓ ∣ Nat.card Kh) : ¬ ℓ ∣ Nat.card (oTwoUpper (N₁ ⊓ (Kh ⊔ N₂))) := by
  intro hd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(oTwoUpper (N₁ ⊓ (Kh ⊔ N₂)))) ℓ hd
  have hyo : orderOf (y : X) = ℓ := by rw [Subgroup.orderOf_coe]; exact hy
  have hyY : (y : X) ∈ N₁ ⊓ (Kh ⊔ N₂) := oTwoUpper_le _ y.2
  have hKN₂ : Kh ≤ Subgroup.normalizer (N₂ : Set X) := hK.trans (sup_le
    (q_normalizes_of_comm hF.comm) Subgroup.le_normalizer)
  have hmul : (↑(Kh ⊔ N₂) : Set X) = ↑Kh * ↑N₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right Kh N₂ hKN₂
  have hy' : (y : X) ∈ (↑(Kh ⊔ N₂) : Set X) := hyY.2
  rw [hmul] at hy'
  obtain ⟨k, hk, b, hb, hkb⟩ := hy'
  have hkey : (y : X) = k * b := hkb.symm
  have hk_eq : k = (y : X) * b⁻¹ := by rw [hkey]; group
  have hc : Commute (y : X) b⁻¹ := hF.comm _ hyY.1 _ (N₂.inv_mem hb)
  obtain ⟨m, hm⟩ : ∃ m, m = orderOf k := ⟨_, rfl⟩
  have hkm : k ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one k
  rw [hk_eq, hc.mul_pow] at hkm
  have h1 : (y : X) ^ m ∈ N₁ ⊓ N₂ := by
    refine ⟨N₁.pow_mem hyY.1 _, ?_⟩
    have : (y : X) ^ m = ((b⁻¹) ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hkm
    rw [this]
    exact N₂.inv_mem (N₂.pow_mem (N₂.inv_mem hb) _)
  rw [hF.disj, Subgroup.mem_bot] at h1
  have hdvd : ℓ ∣ orderOf k := by rw [← hm, ← hyo]; exact orderOf_dvd_of_pow_eq_one h1
  have hk' := orderOf_dvd_natCard (⟨k, hk⟩ : Kh)
  rw [Subgroup.orderOf_mk] at hk'
  exact hKℓ (hdvd.trans hk')

end Odd

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G}

theorem q_inner_of_mem_hatT (h12 : Stage14612PartP) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ 3) (hmax : PMaximal T M 3)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T) (hsG : s ∈ mcOf T)
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (hF : CaseIFacts (imageOTwoQuot (mcOf T) K₁) (imageOTwoQuot (mcOf T) (conjSub s K₁))
      (qPi (mcOf T) ⟨s, hsG⟩))
    (hL : Nonempty (↥(imageOTwoQuot (mcOf T) K₁) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hbot : imageOTwoQuot (mcOf T) K₁ ≠ ⊥)
    {t : OTwoQuot (mcOf T)} (ht : t ∈ imageOTwoQuot (mcOf T) T)
    (htN : t ∈ Subgroup.normalizer (imageOTwoQuot (mcOf T) K₁ : Set (OTwoQuot (mcOf T)))) :
    ∃ g ∈ imageOTwoQuot (mcOf T) K₁, ∀ m ∈ imageOTwoQuot (mcOf T) K₁,
      t * m * t⁻¹ = g * m * g⁻¹ := by
  classical
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂ : conjSub s K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hsG
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp hK₂
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  set N₁ := imageOTwoQuot (mcOf T) K₁ with hN₁
  set N₂ := imageOTwoQuot (mcOf T) (conjSub s K₁) with hN₂
  set Kh := imageOTwoQuot (mcOf T) (oTwoUpper H) with hKh
  set That := imageOTwoQuot (mcOf T) T with hThat
  have hKhle : Kh ≤ N₁ ⊔ N₂ := by
    calc Kh ≤ imageOTwoQuot (mcOf T) (K₁ ⊔ conjSub s K₁) :=
          q_image_mono (hKz ▸ le_conjClosure _ _)
      _ = N₁ ⊔ N₂ := q_image_sup hK₁G hK₂G
  have hTK : ∀ z ∈ That, z ∈ Subgroup.normalizer (Kh : Set (OTwoQuot (mcOf T))) := fun z hz =>
    q_image_mem_normalizer (hred.isHTM.1.1.trans (le_normalizer_oTwoUpper H)) hz
  have key : ∀ z ∈ That, z ∈ Subgroup.normalizer (N₁ : Set (OTwoQuot (mcOf T))) →
      z ∈ Subgroup.normalizer ((oTwoUpper (N₁ ⊓ (Kh ⊔ N₂)) : Subgroup (OTwoQuot (mcOf T))) :
        Set (OTwoQuot (mcOf T))) := by
    intro z hz hzN
    have h2 := q_mem_normalizer_snd hF hbot hzN
    exact normalizer_le_normalizer_oTwoUpper _
      (q_mem_normalizer_inf hzN (q_mem_normalizer_sup (hTK z hz) h2))
  have hNnorm : (N₁ ⊔ N₂) ≤ Subgroup.normalizer ((N₁ ⊔ N₂ : Subgroup (OTwoQuot (mcOf T))) :
      Set (OTwoQuot (mcOf T))) := Subgroup.le_normalizer
  have hSyl0 : IsSylowTwoOf (That ⊓ (N₁ ⊔ N₂)) (N₁ ⊔ N₂) := by
    refine B6.isSylowTwoOf_inf_normal (q_hatT_sylow S) le_top ?_
    exact le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hF.normal).ge
  have hSyl : IsSylowTwoOf (That ⊓ N₁) N₁ := by
    have := B6.isSylowTwoOf_inf_normal hSyl0 (le_sup_left : N₁ ≤ N₁ ⊔ N₂)
      (q_sup_le_normalizer hF)
    rwa [inf_assoc, inf_eq_right.mpr (le_sup_left : N₁ ≤ N₁ ⊔ N₂)] at this
  obtain ⟨E, hEK, hEel, hEcard⟩ := q_exists_elemAbelian_image h12 S hred hmax
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hkE, hk1⟩ : ∃ k ∈ E, k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbotE : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [hbotE, Subgroup.card_bot] at hEcard
    omega
  have hkord : orderOf k = 3 := by
    have h3 : k ^ 3 = 1 := hEel.2 k hkE
    exact orderOf_eq_prime h3 hk1
  have hŝ : (qPi (mcOf T) ⟨s, hsG⟩)⁻¹ ∈ Subgroup.normalizer (Kh : Set (OTwoQuot (mcOf T))) :=
    hTK _ (That.inv_mem ⟨_, Subgroup.mem_subgroupOf.mpr hsT, rfl⟩)
  obtain ⟨y, hyY, hy1, hyodd⟩ := q_exists_odd_mem_inf hF hKhle hŝ Nat.prime_three (by norm_num)
    (hEK hkE) hk1 hkord
  have hYne : oTwoUpper (N₁ ⊓ (Kh ⊔ N₂)) ≠ ⊥ := by
    intro hb
    have := mem_oTwoUpper_of_odd hyY hyodd
    rw [hb, Subgroup.mem_bot] at this
    exact hy1 this
  have h7 : ¬ 7 ∣ Nat.card (oTwoUpper (N₁ ⊓ (Kh ⊔ N₂))) := by
    refine q_not_dvd_card_Y hF hKhle (ℓ := 7) (by norm_num) fun hd => ?_
    have := q_prime_dvd_card_H S hred hmax (by norm_num) (hd.trans (q_card_hatK_dvd S hred))
    omega
  obtain ⟨hL'⟩ := hL
  refine l3_inner_of_normalizes_ambient (N₁ := N₁) (R := That ⊓ N₁)
    (Y := oTwoUpper (N₁ ⊓ (Kh ⊔ N₂))) ⟨hL'⟩ inf_le_right
    ((oTwoUpper_le _).trans inf_le_left) hSyl.2.1 hSyl.2.2
    (fun r hr => key r hr.1 (Subgroup.le_normalizer hr.2)) (S146A.oTwoUpper_idem _) hYne h7 htN ?_
  intro z hz
  exact (Subgroup.mem_normalizer_iff.mp (key t ht htN) z).mp hz

theorem q_wreath_L3 (h12 : Stage14612PartP) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ 3)
    (hmax : PMaximal T M 3) {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nonempty (OTwoQuot (mcOf T) ≃*
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Multiplicative (ZMod 2))) := by
  classical
  obtain ⟨e⟩ := e
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  have hsG : s ∈ mcOf T := hTG hsT
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK₁)
  let e1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥(imageOTwoQuot (mcOf T) K₁) :=
    e.symm.trans eK
  have hLs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    GoldS146P.sl_simple 3 le_rfl
  have hs : IsSimpleGroup ↥(imageOTwoQuot (mcOf T) K₁) := e1.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(imageOTwoQuot (mcOf T) K₁), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := GoldS146P.sl_nonabelian 3 le_rfl
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by simpa using h))⟩
  have hcard : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) = 168 := by
    rw [← Nat.card_congr e1.toEquiv]
    exact SBc15.L3.card_SL32
  have h3 : 3 ∣ Nat.card ↥(imageOTwoQuot (mcOf T) K₁) := by rw [hcard]; norm_num
  have hF := q_caseI_facts h36 hlist iS S hred hmax hK₁ hsG hsN hKz hs hnc h3 h3
  have hbot : imageOTwoQuot (mcOf T) K₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hA : Nat.card (MulAut ↥(imageOTwoQuot (mcOf T) K₁)) =
      2 * Nat.card ↥(imageOTwoQuot (mcOf T) K₁) := by
    rw [← Nat.card_congr (MulAut.congr e1).toEquiv, hcard]
    rw [Nat.card_congr (MulAut.congr (slEquivGL 3)).toEquiv]
    rw [CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  have hNn := hF.normal
  have hq := q_isPGroup_quotient_of_card_aut hF hbot hA
  have hPi : ¬ 2 ∣ (imageOTwoQuot (mcOf T) T).index := by
    have := (q_hatT_sylow S).2.2
    rwa [show ((imageOTwoQuot (mcOf T) T).subgroupOf ⊤).index = (imageOTwoQuot (mcOf T) T).index
      from Subgroup.relIndex_top_right _] at this
  have hinner : ∀ x : OTwoQuot (mcOf T),
      (imageOTwoQuot (mcOf T) K₁).map (MulAut.conj x).toMonoidHom = imageOTwoQuot (mcOf T) K₁ →
      ∃ d : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∀ n ∈ imageOTwoQuot (mcOf T) K₁,
        x * n * x⁻¹ = (e1 d : OTwoQuot (mcOf T)) * n * (e1 d : OTwoQuot (mcOf T))⁻¹ := by
    intro x hx
    have hxN := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hx
    obtain ⟨n, hn, t, ht, rfl⟩ := q_exists_mul_of_sylow hq hPi x
    have htN : t ∈ Subgroup.normalizer (imageOTwoQuot (mcOf T) K₁ : Set (OTwoQuot (mcOf T))) := by
      have : t = n⁻¹ * (n * t) := by group
      rw [this]
      exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem
        (q_sup_le_normalizer hF hn)) hxN
    obtain ⟨g, hg, hgt⟩ := q_inner_of_mem_hatT h12 S hred hmax hK₁ hsT hsG hKz hF ⟨e1.symm⟩ hbot
      ht htN
    obtain ⟨a, ha, b, hb, rfl⟩ := q_exists_mul_of_mem_sup hF hn
    refine ⟨e1.symm ⟨a * g, (imageOTwoQuot (mcOf T) K₁).mul_mem ha hg⟩, fun m hm => ?_⟩
    have hcoe : ((e1 (e1.symm ⟨a * g, (imageOTwoQuot (mcOf T) K₁).mul_mem ha hg⟩) :
        ↥(imageOTwoQuot (mcOf T) K₁)) : OTwoQuot (mcOf T)) = a * g := by
      rw [MulEquiv.apply_symm_apply]
    rw [hcoe]
    have hgm : g * m * g⁻¹ ∈ imageOTwoQuot (mcOf T) K₁ :=
      (imageOTwoQuot (mcOf T) K₁).mul_mem ((imageOTwoQuot (mcOf T) K₁).mul_mem hg hm)
        ((imageOTwoQuot (mcOf T) K₁).inv_mem hg)
    have hbc : b * (g * m * g⁻¹) * b⁻¹ = g * m * g⁻¹ := by
      rw [← hF.comm _ hgm b hb]
      group
    calc a * b * t * m * (a * b * t)⁻¹ = a * (b * (t * m * t⁻¹) * b⁻¹) * a⁻¹ := by group
      _ = a * (b * (g * m * g⁻¹) * b⁻¹) * a⁻¹ := by rw [hgt m hm]
      _ = a * (g * m * g⁻¹) * a⁻¹ := by rw [hbc]
      _ = a * g * m * (a * g)⁻¹ := by group
  have hcardW : 2 * Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ^ 2 ≤
      Nat.card (OTwoQuot (mcOf T)) := by
    rw [Nat.card_congr e1.toEquiv]
    exact q_card_lower_wreath hF hbot
  exact q_mulEquiv_wreath_inner _ _ (qPi (mcOf T) ⟨s, hsG⟩) e1 hF.conj hF.comm hF.disj hF.perm
    hF.normal hF.cen hF.centreless hinner hcardW

end Main

end CFSG.Quasithin
