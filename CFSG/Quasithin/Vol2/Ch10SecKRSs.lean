module

public import CFSG.Quasithin.Vol2.Ch10SecKRSr
public import CFSG.Quasithin.Vol2.Ch10SecKRSk
public import CFSG.Quasithin.Vol2.Ch10SecKRSn
public import CFSG.Quasithin.Vol2.Ch10SecKRSo
public import CFSG.Quasithin.Vol2.Ch10SecKRSq

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_alt (c : Conf T L I t w J)
    (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : FactK7L5)
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (e5 : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (C : AltCoord J (VI T L I J w))
    (hU : ∀ g ∈ uniSL 5, ∃ j : ↥J, C.ρ j = g ∧ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    (huW : t * w * t⁻¹ ∈ VI T L I J w) (hu1 : t * w * t⁻¹ ≠ 1)
    (h3 : InvStd (piL C.ρ c.le).range 3)
    (htriv : ∀ x ∈ (piL C.ρ c.le).range, ∀ v, x • v + v ∈ stdE 5 3)
    (hqX : Nonempty (↥(piL C.ρ c.le).range ⧸ CFSG.pCore 2 ↥(piL C.ρ c.le).range ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hUN : uniSL 5 ≤ Subgroup.normalizer ((piL C.ρ c.le).range : Set SL5)) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hX3 : (piL C.ρ c.le).range = X3 := eq_X3_of_E3 h3 htriv hqX hUN
  have hEu : C.E (t * w * t⁻¹) = B0 := C.E_eq_B0 huW hu1 fun g hg => by
    obtain ⟨j, hj, hjT⟩ := hU g hg
    refine ⟨j, hj, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (Conf.Tw_le_centralizer_u c hTw h37 h38 hjT)
    rw [this]
    group
  have hcen := C.mem_centralizer_iff huW hEu
  have hPJ : theta (CE t w) ≤ J := Conf.theta_CE_le_J c h38 h318 h36' hE hK7L5 hVe hq e5 eJ
  have hQ : ∀ x : ↥(theta (CE t w)), C.ρ (Subgroup.inclusion hPJ x) ∈ Q2 := fun x =>
    mem_Q2_of_conj_B0 ((hcen (Subgroup.inclusion hPJ x)).mp (theta_le _ x.2).1)
  have hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1 := fun j hj => C.ker_two hCJ hj
  have hμs := muQ2_surjective C.ρ C.ρ_surj hker hPJ hQ fun j hj3 hjB =>
    mem_theta ⟨(hcen j).mpr hjB, c.J_le j.2⟩ hj3
  have hkerL : ∀ l : ↥L, piL C.ρ c.le l = 1 → ∃ k : ℕ, l ^ 2 ^ k = 1 := fun l hl => by
    obtain ⟨m, hm⟩ := hker _ hl
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  obtain ⟨c₀, hc₀3, hc₀ρ⟩ := exists_three_lift (piL C.ρ c.le) hkerL
    (hX3 ▸ dS_mem_X3 : dS ∈ (piL C.ρ c.le).range) dS_pow
  have hc₀J : (c₀ : G) ∈ J := c.le c₀.2
  have hc₀ρ' : C.ρ ⟨c₀, hc₀J⟩ = dS := hc₀ρ
  have hc₀3' : (c₀ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hc₀3
  have hc₀CE : (c₀ : G) ∈ CE t w :=
    ⟨(hcen ⟨c₀, hc₀J⟩).mpr (by rw [hc₀ρ']; exact dS_conj_B0), c.J_le hc₀J⟩
  have hc₀P : (c₀ : G) ∈ theta (CE t w) := mem_theta hc₀CE hc₀3'
  have hdCE := Conf.conj_mem_CE c hTw h37 h38 hc₀CE
  have hd3 : (t⁻¹ * (c₀ : G) * t) ^ 3 = 1 := by
    rw [show t⁻¹ * (c₀ : G) * t = t⁻¹ * (c₀ : G) * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hc₀3']
    group
  have hdP : t⁻¹ * (c₀ : G) * t ∈ theta (CE t w) := mem_theta hdCE hd3
  have hdJ : t⁻¹ * (c₀ : G) * t ∈ J := hPJ hdP
  have hdLt : t⁻¹ * (c₀ : G) * t ∈ CFSG.conjugate L t := by
    rw [SecA.mem_conjugate_iff, show t * (t⁻¹ * (c₀ : G) * t) * t⁻¹ = c₀ by group]
    exact c₀.2
  have hdN := rho_mem_normalizer C.ρ c.le hdJ (conjugate_le_normalizer c.hyp c.ht hdLt)
  have hdc := rho_comm_mem_pCoreOf C.ρ c.le hdJ (Conf.comm_mem_of_conjugate c h37 hdLt)
  obtain ⟨-, hdfix⟩ := normalizer_E3 h3 htriv hqX hdN hdc
  set μ := muQ2 C.ρ hPJ hQ with hμ
  have hμc : μ ⟨c₀, hc₀P⟩ = 1 := by
    rw [hμ, muQ2_apply]
    have h1 : (⟨C.ρ (Subgroup.inclusion hPJ ⟨c₀, hc₀P⟩), hQ ⟨c₀, hc₀P⟩⟩ : ↥(stabStd 2 3)) =
        ⟨dS, dS_mem_Q2⟩ := Subtype.ext hc₀ρ'
    rw [h1]
    exact Subtype.ext botB_dS
  have hμd : μ ⟨t⁻¹ * (c₀ : G) * t, hdP⟩ ≠ 1 := by
    intro h
    set g := C.ρ ⟨t⁻¹ * (c₀ : G) * t, hdJ⟩ with hg
    have hgQ : g ∈ Q2 := hQ ⟨_, hdP⟩
    rw [hμ, muQ2_apply] at h
    have hbot : botB (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 :=
      congrArg Subtype.val h
    have htop : topB (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
      ext i j
      have := col_of_fix hdfix (a := Fin.castAdd 3 i) (b := Fin.castAdd 3 j) (by simp; omega)
      simp only [topB, Matrix.submatrix_apply]
      rw [this]
      fin_cases i <;> fin_cases j <;> rfl
    have hsq : g * g = 1 := sq_eq_one_of_blocks hgQ htop hbot
    have hg3 : g ^ 3 = 1 := by
      rw [hg, ← map_pow]
      have : (⟨t⁻¹ * (c₀ : G) * t, hdJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, map_one]
    have hg1 : g = 1 := by
      rw [pow_succ, sq, hsq, one_mul] at hg3
      exact hg3
    obtain ⟨m, hm⟩ := hker _ hg1
    have hd1 : t⁻¹ * (c₀ : G) * t = 1 := by
      have h1 : orderOf (t⁻¹ * (c₀ : G) * t) ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
      have h2 : orderOf (t⁻¹ * (c₀ : G) * t) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)) h1 h2)
    have hc1 : (c₀ : G) = 1 := by
      calc (c₀ : G) = t * (t⁻¹ * (c₀ : G) * t) * t⁻¹ := by group
        _ = 1 := by rw [hd1]; group
    apply dS_ne
    rw [← hc₀ρ']
    have : (⟨c₀, hc₀J⟩ : ↥J) = 1 := Subtype.ext hc1
    rw [this, map_one]
  let σ : ↥(theta (CE t w)) ≃* ↥(theta (CE t w)) :=
    { toFun := fun x => ⟨t⁻¹ * (x : G) * t, Conf.conj_mem_theta_CE c hTw h37 h38 x.2⟩
      invFun := fun x => ⟨t * (x : G) * t⁻¹, Conf.conj_mem_theta_CE' c hTw h37 h38 x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  set N₁ := Subgroup.normalClosure ({⟨c₀, hc₀P⟩} : Set ↥(theta (CE t w))) with hN₁
  set N₂ := Subgroup.normalClosure
    ({⟨t⁻¹ * (c₀ : G) * t, hdP⟩} : Set ↥(theta (CE t w))) with hN₂
  have hN : N₂ = N₁.map σ.toMonoidHom := by
    rw [hN₁, Subgroup.map_normalClosure _ σ.toMonoidHom σ.surjective, Set.image_singleton]
    rfl
  have hcard : Nat.card N₂ = Nat.card N₁ := by
    rw [hN]
    exact Subgroup.card_map_of_injective σ.injective
  have h7₁ : ¬ 7 ∣ Nat.card N₁ := by
    intro h7
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have hxk : (x : ↥(theta (CE t w))) ∈ μ.ker :=
      Subgroup.normalClosure_le_normal
        (Set.singleton_subset_iff.mpr (MonoidHom.mem_ker.mpr hμc)) x.2
    have hx7 : orderOf (x : ↥(theta (CE t w))) = 7 := by rw [Subgroup.orderOf_coe]; exact hx
    set y : ↥(stabStd 2 3) := ⟨C.ρ (Subgroup.inclusion hPJ x), hQ x⟩
    have hy7 : y ^ 7 = 1 := by
      apply Subtype.ext
      show (C.ρ (Subgroup.inclusion hPJ x)) ^ 7 = 1
      rw [← map_pow, ← map_pow, ← hx7, pow_orderOf_eq_one, map_one, map_one]
    have hy1 := eq_one_of_botH (g := y) hxk hy7
    have hρ1 : C.ρ (Subgroup.inclusion hPJ x) = 1 := congrArg Subtype.val hy1
    obtain ⟨m, hm⟩ := hker _ hρ1
    have h1 : orderOf ((x : ↥(theta (CE t w))) : G) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    rw [Subgroup.orderOf_coe, hx7] at h1
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h1))
    norm_num at this
  have h7₂ : 7 ∣ Nat.card N₂ := by
    obtain ⟨z, hz, hz7⟩ := exists_seven_of_ne hμd
    have hmap : N₂.map μ = Subgroup.normalClosure {μ ⟨t⁻¹ * (c₀ : G) * t, hdP⟩} := by
      rw [hN₂, Subgroup.map_normalClosure _ μ hμs, Set.image_singleton]
    rw [← hmap] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have h1 : orderOf (μ x) ∣ orderOf (⟨x, hx⟩ : ↥N₂) := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_map_dvd μ x
    rw [hz7] at h1
    exact h1.trans (orderOf_dvd_natCard _)
  exact h7₁ (hcard ▸ h7₂)

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
