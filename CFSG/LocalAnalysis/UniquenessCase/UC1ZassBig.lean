module

public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassPGL
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassQuad
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassQuat
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassStab
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassTame
public import CFSG.RankThree.PartTwo.Sec16.Item167ProofGL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open TensorProduct QuaternionGroup

theorem sixteen_dvd_of_mul_eq {k r u : ℕ} (hk1 : 0 < k) (hk2 : k ≤ 2) (h8 : 8 ∣ u)
    (h : k * r = 4 * u) : 16 ∣ r := by
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl <;> omega

theorem no_fpf_of_quaternion_cycle {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {ρ : Representation (ZMod p) G V} (hρ : Function.Injective ρ)
    (hf : Fpf ρ) {S : Sylow 2 G} {t : ℕ} (ht : 3 ≤ t) (e : S ≃* QuaternionGroup (2 ^ t))
    {i j w z : G} (hiS : i ∈ S) (hjS : j ∈ S) (hz : z ^ 2 = 1) (hz1 : z ≠ 1) (hi : i ^ 2 = z)
    (hj : j ^ 2 = z) (hji : j * i * j⁻¹ = i⁻¹) (hw3 : w ^ 3 = 1) (hwi : w * i * w⁻¹ = j)
    (hwj : w * j * w⁻¹ = i * j) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial G := ⟨⟨z, 1, hz1⟩⟩
  haveI : Nontrivial V := nontrivial_of_injective hρ
  have hpG : ¬ p ∣ Nat.card G := hf.not_dvd_card
  let K := GaloisField p (2 ^ t)
  have hk : (2 : K) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h2
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_galoisField p hp t
  have hfK : Fpf (ρ.baseChange K) := hf.baseChange K
  haveI : Nontrivial (K ⊗[ZMod p] V) := inferInstance
  have hzo : orderOf z = 2 := orderOf_eq_prime hz hz1
  let φ : QuaternionGroup (2 ^ t) →* G := (S : Subgroup G).subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hz0o : orderOf (φ (a ((2 ^ t : ℕ) : ZMod (2 * 2 ^ t)))) = 2 := by
    rw [orderOf_injective φ hφ, ← a_one_pow, orderOf_pow_of_dvd (by positivity)
      (by rw [orderOf_a_one]; exact Dvd.intro_left 2 rfl), orderOf_a_one]
    exact Nat.mul_div_cancel 2 (by positivity)
  have hzz : z = φ (a ((2 ^ t : ℕ) : ZMod (2 * 2 ^ t))) := hfK.eq_of_orderOf_eq_two hzo hz0o
  obtain ⟨W, hW, hWQ, hWsc⟩ := exists_plane_of_quaternion (ρ.baseChange K) hk (by omega) hζ hφ
    (fun v => hfK.apply_eq_neg hz0o v)
  have hWS : ∀ s ∈ (S : Subgroup G), ∀ x ∈ W, (ρ.baseChange K) s x ∈ W := by
    intro s hs x hx
    simpa [φ] using hWQ (e ⟨s, hs⟩) x hx
  have hsc : ∀ s ∈ (S : Subgroup G),
      (∃ μ : K, ∀ x ∈ W, (ρ.baseChange K) s x = μ • x) → s = 1 ∨ s = z := by
    intro s hs hsc'
    have hφs : φ (e ⟨s, hs⟩) = s := by simp [φ]
    rcases hWsc (e ⟨s, hs⟩) (by rwa [hφs]) with h | h
    · left
      rw [← hφs, h, map_one]
    · right
      rw [← hφs, h, ← hzz]
  have hzS : z ∈ (S : Subgroup G) := hi ▸ Subgroup.pow_mem _ hiS 2
  have hzc : ∀ g : G, g * z = z * g := by
    intro g
    have hgz : orderOf (g * z * g⁻¹) = 2 := by
      have h1 : (g * z * g⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hz]
        group
      refine orderOf_eq_prime h1 ?_
      intro h
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact mul_inv_eq_iff_eq_mul.mp (hfK.eq_of_orderOf_eq_two hgz hzo)
  have hi1 : i ≠ 1 := by
    rintro rfl
    exact hz1 (by rw [← hi, one_pow])
  have hiz : i ≠ z := by
    intro h
    apply hz1
    rw [← hi, h]
    exact hz
  have hj1 : j ≠ 1 := by
    rintro rfl
    exact hz1 (by rw [← hj, one_pow])
  have hjz : j ≠ z := by
    intro h
    apply hz1
    rw [← hj, h]
    exact hz
  have hji0 : j * i = i⁻¹ * j := mul_inv_eq_iff_eq_mul.mp hji
  have hz_inv : i⁻¹ = z * i :=
    (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, ← sq, hi, ← sq, hz])).symm
  have hji' : j * i = z * i * j := by rw [hji0, hz_inv]
  have hcomm : j * i = i * j → False := by
    intro h
    have h1 : i = i⁻¹ := by
      calc i = i * j * j⁻¹ := by group
        _ = j * i * j⁻¹ := by rw [h]
        _ = i⁻¹ := hji
    exact hz1 (by rw [← hi, sq]; exact mul_eq_one_iff_eq_inv.mpr h1)
  have ha2 : (z * i) ^ 2 = z := by
    rw [Commute.mul_pow ((hzc i).symm : Commute z i), hz, hi, one_mul]
  have hwzw : w * z * w⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr (hzc w)
  have hwa : w * (z * i) * w⁻¹ = z * j := by
    calc w * (z * i) * w⁻¹ = (w * z * w⁻¹) * (w * i * w⁻¹) := by group
      _ = z * j := by rw [hwzw, hwi]
  have hb2 : (w * (z * i) * w⁻¹) ^ 2 = z := by
    rw [hwa, Commute.mul_pow ((hzc j).symm : Commute z j), hz, hj, one_mul]
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hcomm (by rw [show j = i by simpa using hwi.symm])
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hij2 : (i * j) ^ 2 = z := by
    calc (i * j) ^ 2 = i * (j * i) * j := by rw [sq]; group
      _ = i * (i⁻¹ * j) * j := by rw [hji0]
      _ = j ^ 2 := by rw [sq]; group
      _ = z := hj
  have haw3 : (z * i * w) ^ 3 = 1 := by
    have h1 : (i * w) ^ 3 = i * (w * i * w⁻¹) * (w * (w * i * w⁻¹) * w⁻¹) * w ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    have h2 : (i * w) ^ 3 = z := by
      rw [h1, hwi, hwj, hw3, mul_one, ← hij2, sq, mul_assoc]
    rw [mul_assoc, Commute.mul_pow ((hzc (i * w)).symm : Commute z (i * w)), h2, ← pow_succ,
      show 3 + 1 = 2 * 2 from rfl, pow_mul, hz, one_pow]
  have haw1 : z * i * w ≠ 1 := by
    intro h
    have h3 : (z * i) ^ 3 = 1 := by
      have := hw3
      rw [eq_inv_of_mul_eq_one_right h, inv_pow, inv_eq_one] at this
      exact this
    have h4 : (z * i) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2, hz]
    have h5 : z * i = 1 := by
      calc z * i = (z * i) ^ 4 * ((z * i) ^ 3)⁻¹ := by group
        _ = 1 := by rw [h3, h4]; simp
    exact hz1 (by rw [← ha2, h5, one_pow])
  have hwo3 : orderOf (z * i * w) = 3 := orderOf_eq_prime haw3 haw1
  have hzziS : z * i ∈ (S : Subgroup G) := S.mul_mem hzS hiS
  have hzjS : z * j ∈ (S : Subgroup G) := S.mul_mem hzS hjS
  have hwW : ∀ x ∈ W, (ρ.baseChange K) w x ∈ W := fun x hx =>
    hfK.mem_of_quad hk hwo hwo3 hzo ha2 hb2 (fun y hy => hWS _ hzziS y hy)
      (fun y hy => by rw [hwa]; exact hWS _ hzjS y hy) hx
  have hSR : (S : Subgroup G) ≤ stab (ρ.baseChange K) W := fun s hs => hWS s hs
  obtain ⟨θ, hθ⟩ := exists_hom_pgl (ρ.baseChange K) W hW (stab (ρ.baseChange K) W)
    (fun g hg => mem_stab.mp hg)
  haveI : Finite θ.range := Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  let iR : stab (ρ.baseChange K) W := ⟨i, hSR hiS⟩
  let jR : stab (ρ.baseChange K) W := ⟨j, hSR hjS⟩
  let wR : stab (ρ.baseChange K) W := ⟨w, hwW⟩
  let zR : stab (ρ.baseChange K) W := ⟨z, hSR hzS⟩
  have hθz : θ zR = 1 := (hθ zR).2 ⟨-1, fun x _ => by
    rw [neg_one_smul]
    exact hfK.apply_eq_neg hzo x⟩
  let θ' : stab (ρ.baseChange K) W →* θ.range := θ.rangeRestrict
  have hθ' : ∀ g, θ' g = 1 ↔ θ g = 1 := fun g => Subtype.ext_iff.trans Iff.rfl
  have hnot : ∀ (s : G) (hs : s ∈ (S : Subgroup G)), s ≠ 1 → s ≠ z → θ ⟨s, hSR hs⟩ ≠ 1 := by
    intro s hs h1 h2 h
    rcases hsc s hs ((hθ ⟨s, hSR hs⟩).1 h) with h' | h'
    exacts [h1 h', h2 h']
  have hα1 : θ' iR ≠ 1 := fun h => hnot i hiS hi1 hiz ((hθ' iR).1 h)
  have hβ1 : θ' jR ≠ 1 := fun h => hnot j hjS hj1 hjz ((hθ' jR).1 h)
  have hne : θ' iR ≠ θ' jR := by
    intro h
    have h1 : θ' (iR⁻¹ * jR) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hsc (i⁻¹ * j) (S.mul_mem (S.inv_mem hiS) hjS)
      ((hθ (iR⁻¹ * jR)).1 ((hθ' _).1 h1))
    apply hcomm
    rcases h2 with h2 | h2
    · rw [inv_mul_eq_one.mp h2]
    · calc j * i = i * z * i := by rw [inv_mul_eq_iff_eq_mul.mp h2]
        _ = i * (z * i) := mul_assoc _ _ _
        _ = i * j := by rw [← hzc i, ← inv_mul_eq_iff_eq_mul.mp h2]
  have hβ2 : θ' jR ^ 2 = 1 := by
    rw [← map_pow, show jR ^ 2 = zR from Subtype.ext hj]
    exact (hθ' zR).2 hθz
  have hαβ : θ' iR * θ' jR = θ' jR * θ' iR := by
    rw [← map_mul, ← map_mul]
    have h1 : jR * iR = zR * (iR * jR) := Subtype.ext (by
      show j * i = z * (i * j)
      rw [hji', mul_assoc])
    rw [h1, map_mul θ' zR, (hθ' zR).2 hθz, one_mul]
  have hω : θ' wR * θ' iR * (θ' wR)⁻¹ = θ' jR := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg θ' (Subtype.ext hwi)
  have hω' : θ' wR * θ' jR * (θ' wR)⁻¹ = θ' iR * θ' jR := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg θ' (Subtype.ext hwj)
  have hω3 : θ' wR ^ 3 = 1 := by
    rw [← map_pow, show wR ^ 3 = 1 from Subtype.ext hw3, map_one]
  have hnJ : ¬ p ∣ Nat.card θ.range := fun h =>
    hpG (h.trans ((Subgroup.card_range_dvd θ).trans (Subgroup.card_subgroup_dvd_card _)))
  have hJ := CFSG.RankThree.PartTwo.Sec16.Crit167.pgl_tame_cases_alt (p := p) (k := K) θ.range hnJ
  let ψ : (S : Subgroup G) →* θ.range := θ'.comp (Subgroup.inclusion hSR)
  have hψ : ∀ s : (S : Subgroup G), ψ s = 1 → (s : G) = 1 ∨ (s : G) = z := fun s hs =>
    hsc s s.2 ((hθ ⟨s, hSR s.2⟩).1 ((hθ' _).1 hs))
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hsub : (ψ.ker : Set (S : Subgroup G)) ⊆ {1, ⟨z, hzS⟩} := by
      intro k hk
      rcases hψ k hk with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    calc Nat.card ψ.ker = (ψ.ker : Set (S : Subgroup G)).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, ⟨z, hzS⟩} : Set (S : Subgroup G)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
  have hcardS : Nat.card (S : Subgroup G) = 4 * 2 ^ t := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = 4 * 2 ^ t := by
    rw [← hcardS, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have h16 : 16 ∣ Nat.card θ.range := by
    have hdvd : Nat.card ψ.range ∣ Nat.card θ.range := Subgroup.card_subgroup_dvd_card ψ.range
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have h8 : 8 ∣ 2 ^ t := by simpa using Nat.pow_dvd_pow 2 ht
    exact (sixteen_dvd_of_mul_eq hpos hker h8 hcard).trans hdvd
  exact false_of_tame_cases hα1 hβ1 hne hβ2 hαβ hω hω' hω3 h16 hJ

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
