module

public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.RankThree.PartOne.K159.CoverLift

public section

namespace CFSG.RankThree.PartOne.K159

open scoped commutatorElement
open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.RankThree.Classical
  CFSG.RankThree.Classical2

section Witness

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_elemAbelian_unitary_witness {Y : Type*} [Group Y] [Finite Y]
    (hK : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n)
    (φ : Y →* unitaryPSU hK n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {m : ℕ}
    (c : Fin m → Fin n → Kˣ) (hcp : ∀ j i, c j i ^ p = 1)
    (hcS : ∀ a, diagHom n (@expHom p ⟨hp.ne_zero⟩ _ _ _ _ _ c hcp a) ∈ unitarySU ℓ f K n)
    (hinj : Function.Injective (@expHom p ⟨hp.ne_zero⟩ _ _ _ _ _ c hcp))
    (hswap : ∀ j k, j ≠ k → ∃ w ∈ unitarySU ℓ f K n,
      w * diagHom n (c j) * w⁻¹ = diagHom n (c k) ∧ w * diagHom n (c k) * w⁻¹ = diagHom n (c j))
    (hinv : ∀ j, ∃ w ∈ unitarySU ℓ f K n, w * diagHom n (c j) * w⁻¹ = (diagHom n (c j))⁻¹)
    {z : Y} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    ∃ B : Subgroup Y, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ (m - (if p ∣ n then 1 else 0) + 1) ≤ Nat.card B := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite K := hK.finite
  set S := unitarySU ℓ f K n
  set E := expHom (p := p) c hcp
  let δ : Multiplicative (Fin m → ZMod p) →* S := ((diagHom n).comp E).codRestrict S hcS
  have hδ : ∀ a, (δ a : GL (Fin n) K) = diagHom n (E a) := fun a => rfl
  let θ : Multiplicative (Fin m → ZMod p) →* unitaryPSU hK n := (unitaryProj hK n).comp δ
  set D := θ.range with hDdef
  have hθsingle : ∀ j, (δ (Multiplicative.ofAdd (Pi.single j 1)) : GL (Fin n) K) =
      diagHom n (c j) := fun j => by rw [hδ, expHom_single]
  have hpow : ∀ a : Multiplicative (Fin m → ZMod p), a ^ p = 1 := by
    intro a
    change Multiplicative.ofAdd (p • Multiplicative.toAdd a) = 1
    have : p • Multiplicative.toAdd a = 0 := by
      funext i
      simp [nsmul_eq_mul]
    rw [this]
    rfl
  have hDp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hpow, map_one]
  have hgen : ∀ j k : Fin m, liftComm φ hφ (θ (Multiplicative.ofAdd (Pi.single j 1)))
      (θ (Multiplicative.ofAdd (Pi.single k 1))) = 1 := by
    intro j k
    rcases eq_or_ne j k with rfl | hjk
    · exact liftComm_self hφ _
    obtain ⟨w, hwS, hw1, hw2⟩ := hswap j k hjk
    have hcomm : Commute (θ (Multiplicative.ofAdd (Pi.single j 1)))
        (θ (Multiplicative.ofAdd (Pi.single k 1))) := (Commute.all _ _).map θ
    refine liftComm_eq_one_of_conj_swap hφ hker (hp.odd_of_ne_two hp2) hcomm
      (by rw [← map_pow, hpow, map_one]) (unitaryProj hK n ⟨w, hwS⟩) ?_ ?_
    · change unitaryProj hK n (⟨w, hwS⟩ * δ _ * ⟨w, hwS⟩⁻¹) = unitaryProj hK n (δ _)
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hθsingle, hθsingle, hw1]
    · change unitaryProj hK n (⟨w, hwS⟩ * δ _ * ⟨w, hwS⟩⁻¹) = unitaryProj hK n (δ _)
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hθsingle, hθsingle, hw2]
  have hall : ∀ s ∈ D, ∀ t ∈ D, liftComm φ hφ s t = 1 := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    refine liftComm_eq_one_of_closure hφ hker θ closure_range_single_eq_top ?_ a a'
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
    exact hgen j k
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_liftComm_eq_one hφ hker hall hx hy
  have hscalar : ∀ a, θ a = 1 → ∃ c : Kˣ, c ^ n = 1 ∧ c ^ p = 1 ∧
      diagHom n (E a) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    intro a ha
    have hmem : δ a ∈ unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact ha
    obtain ⟨c, -, hcn, hc⟩ := mem_unitaryScalars.mp hmem
    refine ⟨c, hcn, ?_, by rw [← hδ, hc]⟩
    have h1 : (δ (a ^ p) : GL (Fin n) K) = 1 := by rw [hpow, map_one]; rfl
    rw [map_pow, Subgroup.coe_pow, hc, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
      ⟨0, by omega⟩) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext (by simpa using h2)
  have hkercard : Nat.card θ.ker ≤ p ^ (if p ∣ n then 1 else 0) := by
    split_ifs with hpn
    · rw [pow_one]
      let ev : θ.ker →* Kˣ := ((Pi.evalMonoidHom (fun _ : Fin n => Kˣ) ⟨0, by omega⟩).comp E).comp
        θ.ker.subtype
      have hev : Function.Injective ev := by
        refine (injective_iff_map_eq_one ev).mpr fun x hx => ?_
        obtain ⟨c, -, -, hc⟩ := hscalar x x.2
        have h0 : (c : K) = 1 := by
          have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
            ⟨0, by omega⟩) hc
          simp only [coe_diagHom, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
            Matrix.scalar_apply] at this
          rw [← this]
          exact congrArg Units.val hx
        have hc1 : c = 1 := Units.ext h0
        have h1 : E x = 1 := by
          apply diagHom_injective n
          rw [hc, hc1, map_one, map_one]
        exact Subtype.ext (hinj (h1.trans (map_one E).symm))
      have hrange : ev.range ≤ rootsOfUnity p K := by
        rintro _ ⟨x, rfl⟩
        have hx : x ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
        rw [mem_rootsOfUnity, ← map_pow, hx, map_one]
      calc Nat.card θ.ker = Nat.card ev.range :=
            Nat.card_congr (MonoidHom.ofInjective hev).toEquiv
        _ ≤ Nat.card (rootsOfUnity p K) := Subgroup.card_le_of_le hrange
        _ ≤ p := card_rootsOfUnity K p
    · rw [pow_zero]
      have hbot : θ.ker = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
        obtain ⟨c, hcn, hcp', hc⟩ := hscalar x hx
        have hc1 : c = 1 := by
          have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
          have : c ^ Nat.gcd p n = 1 := pow_gcd_eq_one.mpr ⟨hcp', hcn⟩
          rwa [hcop.gcd_eq_one, pow_one] at this
        have h1 : E x = 1 := by
          apply diagHom_injective n
          rw [hc, hc1, map_one, map_one]
        exact hinj (h1.trans (map_one E).symm)
      rw [hbot, Subgroup.card_bot]
  have hDcard : p ^ (m - if p ∣ n then 1 else 0) ≤ Nat.card D := by
    set ε := if p ∣ n then 1 else 0 with hεdef
    by_cases hε : ε ≤ m
    · have h1 : Nat.card θ.ker * Nat.card D = p ^ m := by
        rw [hDdef, ← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_congr
          Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      have h2 : p ^ m ≤ Nat.card D * p ^ ε := by
        rw [← h1, mul_comm]
        exact Nat.mul_le_mul_left _ hkercard
      have h3 : p ^ m = p ^ (m - ε) * p ^ ε := by
        rw [← pow_add, Nat.sub_add_cancel hε]
      rw [h3] at h2
      exact Nat.le_of_mul_le_mul_right h2 (pow_pos hp.pos _)
    · rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
      exact Nat.card_pos
  set Sg : Set (unitaryPSU hK n) := Set.range fun j : Fin m => θ (Multiplicative.ofAdd (Pi.single j 1))
    with hSg
  have hcl : Subgroup.closure Sg = D := by
    have h1 : (Subgroup.closure (Set.range fun j : Fin m =>
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) :
          Multiplicative (Fin m → ZMod p)))).map θ = Subgroup.closure Sg := by
      rw [MonoidHom.map_closure, hSg, ← Set.range_comp]
      rfl
    rw [← h1, closure_range_ofAdd_single, ← MonoidHom.range_eq_map]
  have hSp : ∀ s ∈ Sg, s ^ p = 1 := fun s hs => hDp s (by
    rw [← hcl]
    exact Subgroup.subset_closure hs)
  have hSinv : ∀ s ∈ Sg, ∃ g : unitaryPSU hK n, g * s * g⁻¹ = s⁻¹ := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨w, hwS, hw⟩ := hinv j
    refine ⟨unitaryProj hK n ⟨w, hwS⟩, ?_⟩
    show unitaryProj hK n ⟨w, hwS⟩ * unitaryProj hK n (δ (Multiplicative.ofAdd (Pi.single j 1))) *
      (unitaryProj hK n ⟨w, hwS⟩)⁻¹ = (unitaryProj hK n (δ (Multiplicative.ofAdd (Pi.single j 1))))⁻¹
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hθsingle, hw]
  have hF' : ∀ x ∈ (Subgroup.closure Sg).comap φ, ∀ y ∈ (Subgroup.closure Sg).comap φ,
      x * y = y * x := by
    rw [hcl]
    exact hF
  obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_card_ge hφ hker hodd hp Sg hSp hSinv hF' hz hz1
    hzp
  refine ⟨B, hBp, hBc, ?_⟩
  rw [hcl] at hBcard
  calc p ^ (m - (if p ∣ n then 1 else 0) + 1)
      = p * p ^ (m - (if p ∣ n then 1 else 0)) := by rw [pow_succ, mul_comm]
    _ ≤ p * Nat.card D := Nat.mul_le_mul_left _ hDcard
    _ ≤ Nat.card B := hBcard

end Witness

section Main

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem neg_one_pow_norm (hK : UnitaryFieldData ℓ f K) : (-1 : K) ^ (ℓ ^ f + 1) = 1 := by
  by_cases hℓ2 : ℓ = 2
  · have hchar : CharP K 2 := hℓ2 ▸ hK.charP
    have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hneg : (-1 : K) = 1 := by linear_combination -h2K
    rw [hneg, one_pow]
  · have hℓodd : Odd ℓ := hK.prime.odd_of_ne_two hℓ2
    exact ((hℓodd.pow).add_one).neg_one_pow

theorem exists_elemAbelian_unitary {Y : Type*} [Group Y] [Finite Y]
    (hK : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f + 1)
    {n : ℕ} (hn : 3 ≤ n) (φ : Y →* unitaryPSU hK n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {z : Y} (hz : z ∈ φ.ker)
    (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    ∃ B : Subgroup Y, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ (n - 1 - (if p ∣ n then 1 else 0) + 1) ≤ Nat.card B := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one hK hp hpq
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hn1 : 1 ≤ m + 3 := by omega
  set c : Fin (m + 2) → Fin (m + 3) → Kˣ := fun j i =>
    if i = 0 then ζ else if i = j.succ then ζ⁻¹ else 1 with hcdef
  have hcp : ∀ j i, c j i ^ p = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζp
    · rw [inv_pow, hζp, inv_one]
    · exact one_pow p
  have hcnorm : ∀ j i, c j i ^ (ℓ ^ f + 1) = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζN
    · rw [inv_pow, hζN, inv_one]
    · exact one_pow _
  have hcprod : ∀ j, ∏ i, c j i = 1 := by
    intro j
    rw [Fin.prod_univ_succ]
    have h0 : c j 0 = ζ := by simp [hcdef]
    have h1 : ∀ i : Fin (m + 2), c j i.succ = if i = j then ζ⁻¹ else 1 := by
      intro i
      simp only [hcdef, Fin.succ_ne_zero, ite_false, Fin.succ_inj]
    simp only [h0, h1, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    group
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
    intro j
    refine ⟨j.succ, fun j' hj' => ?_, ?_⟩
    · simp only [hcdef, Fin.succ_ne_zero, ite_false, Fin.succ_inj]
      simp [hj'.symm]
    · simp only [hcdef, Fin.succ_ne_zero, ite_false, ite_true]
      rw [orderOf_inv, hζ]
  set d₁ : Fin (m + 3) → Kˣ := fun i => if i = 0 then -1 else 1 with hd₁
  have hd₁norm : ∀ i, ((d₁ i : Kˣ) : K) ^ (ℓ ^ f + 1) = 1 := by
    intro i
    simp only [hd₁]
    split_ifs
    · rw [Units.val_neg, Units.val_one]
      exact neg_one_pow_norm hK
    · rw [Units.val_one, one_pow]
  have hwS : ∀ a b : Fin (m + 3), a ≠ b →
      permGL (Equiv.swap a b) * diagHom (m + 3) d₁ ∈ unitarySU ℓ f K (m + 3) := by
    intro a b hab
    rw [mem_unitarySU_iff hK, Units.val_mul]
    refine ⟨?_, unitary_mul hK (permGL_unitary hK _) (diagHom_unitary hK hd₁norm)⟩
    rw [Matrix.det_mul, det_permGL, Equiv.Perm.sign_swap hab, det_diagHom, Fin.prod_univ_succ]
    simp [hd₁, Fin.succ_ne_zero]
  have hconj : ∀ (σ : Equiv.Perm (Fin (m + 3))) (e : Fin (m + 3) → Kˣ),
      (permGL σ * diagHom (m + 3) d₁) * diagHom (m + 3) e * (permGL σ * diagHom (m + 3) d₁)⁻¹ =
        diagHom (m + 3) (e ∘ σ.symm) := by
    intro σ e
    rw [← permGL_mul_diagHom_mul_inv σ e]
    have hcomm := (diagHom_commute (K := K) d₁ e).eq
    calc (permGL σ * diagHom (m + 3) d₁) * diagHom (m + 3) e *
          (permGL σ * diagHom (m + 3) d₁)⁻¹ =
        permGL σ * (diagHom (m + 3) d₁ * diagHom (m + 3) e) * (diagHom (m + 3) d₁)⁻¹ *
          (permGL σ)⁻¹ := by group
      _ = permGL σ * (diagHom (m + 3) e * diagHom (m + 3) d₁) * (diagHom (m + 3) d₁)⁻¹ *
          (permGL σ)⁻¹ := by rw [hcomm]
      _ = permGL σ * diagHom (m + 3) e * (permGL σ)⁻¹ := by group
  have hswap : ∀ j k, j ≠ k → ∃ w ∈ unitarySU ℓ f K (m + 3),
      w * diagHom (m + 3) (c j) * w⁻¹ = diagHom (m + 3) (c k) ∧
        w * diagHom (m + 3) (c k) * w⁻¹ = diagHom (m + 3) (c j) := by
    intro j k hjk
    have hjk' : j.succ ≠ k.succ := fun h => hjk (Fin.succ_injective _ h)
    have hcσ : ∀ a b : Fin (m + 2), c a ∘ (Equiv.swap a.succ b.succ).symm = c b := by
      intro a b
      funext i
      rw [Function.comp_apply, Equiv.symm_swap]
      have hs0 : Equiv.swap a.succ b.succ 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm
      simp only [hcdef, Equiv.swap_apply_eq_iff, hs0, Equiv.swap_apply_left]
    refine ⟨_, hwS _ _ hjk', ?_, ?_⟩
    · rw [hconj, hcσ]
    · rw [hconj, Equiv.swap_comm, hcσ]
  have hinv : ∀ j, ∃ w ∈ unitarySU ℓ f K (m + 3),
      w * diagHom (m + 3) (c j) * w⁻¹ = (diagHom (m + 3) (c j))⁻¹ := by
    intro j
    have h0j : (0 : Fin (m + 3)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    refine ⟨_, hwS _ _ h0j, ?_⟩
    rw [hconj, ← map_inv]
    congr 1
    funext i
    rw [Function.comp_apply, Equiv.symm_swap, Pi.inv_apply]
    by_cases hi0 : i = 0
    · subst hi0
      rw [Equiv.swap_apply_left]
      simp [hcdef]
    by_cases hij : i = j.succ
    · subst hij
      rw [Equiv.swap_apply_right]
      simp [hcdef]
    · rw [Equiv.swap_apply_of_ne_of_ne hi0 hij]
      simp [hcdef, hi0, hij]
  have := exists_elemAbelian_unitary_witness hK hp hp2 hn1 φ hφ hker hodd c hcp
    (diagHom_expHom_mem_unitarySU hK c hcp hcprod hcnorm) (expHom_injective c hcp hpriv) hswap
    hinv hz hz1 hzp
  obtain ⟨B, hBp, hBc, hBcard⟩ := this
  exact ⟨B, hBp, hBc, by simpa using hBcard⟩

end Main

end CFSG.RankThree.PartOne.K159
