module

public import CFSG.RankThree.PartTwo.Sec12.Coordinates
import CFSG.RankThree.PartTwo.Sec3.TransvectionSylowCentralizer
import CFSG.RankThree.PartTwo.Sec18.Item1810Transv
import CFSG.RankThree.PartTwo.Sec18.Item1810Linear
import CFSG.RankThree.PartTwo.Sec18.Item1810Act

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item1810Proof

open CFSG CFSG.RankThree.PartTwo

variable {G : Type*} [Group G] [Finite G]

section Aux

variable {D : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
  (f : Multiplicative V ≃* D)

private theorem coordVec_congr {y z : G} (hy : y ∈ D) (hz : z ∈ D) (h : y = z) :
    Sec12.coordVec f ⟨y, hy⟩ = Sec12.coordVec f ⟨z, hz⟩ := by
  subst h
  rfl

private theorem coordVec_inv {y : G} (hy : y ∈ D) :
    Sec12.coordVec f ⟨y⁻¹, D.inv_mem hy⟩ = -Sec12.coordVec f ⟨y, hy⟩ := by
  have h := coordVec_zpow f hy (-1)
  have h2 : Sec12.coordVec f ⟨y⁻¹, D.inv_mem hy⟩ =
      Sec12.coordVec f ⟨y ^ (-1 : ℤ), D.zpow_mem hy (-1)⟩ :=
    coordVec_congr f _ _ (zpow_neg_one y).symm
  rw [h2, h]
  simp

private theorem wAction_coordVec_zpow (n : Subgroup.normalizer (D : Set G)) {y z : G}
    (hy : y ∈ D) (hz : z ∈ D) {i : ℤ} (h : (n : G) * y * (n : G)⁻¹ = z ^ i) :
    Sec12.wAction f n (Sec12.coordVec f ⟨y, hy⟩) = (i : ZMod 3) • Sec12.coordVec f ⟨z, hz⟩ := by
  rw [wAction_coordVec f n hy, ← coordVec_zpow f hz i]
  exact coordVec_congr f _ _ h

private theorem wAction_mem_of_mem_sup {A B : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (D : Set G)) (hBN : B ≤ Subgroup.normalizer (D : Set G))
    (H : Subgroup (V ≃ₗ[ZMod 3] V))
    (hA : ∀ (a : G) (ha : a ∈ A), Sec12.wAction f ⟨a, hAN ha⟩ ∈ H)
    (hB : ∀ (b : G) (hb : b ∈ B), Sec12.wAction f ⟨b, hBN hb⟩ ∈ H) {k : G} (hk : k ∈ A ⊔ B) :
    Sec12.wAction f ⟨k, sup_le hAN hBN hk⟩ ∈ H := by
  have hle : (A ⊔ B).subgroupOf (Subgroup.normalizer (D : Set G)) ≤
      H.comap (Sec12.wAction f) := by
    rw [Subgroup.subgroupOf_sup hAN hBN]
    exact sup_le (fun n hn => hA n hn) (fun n hn => hB n hn)
  exact hle (Subgroup.mem_subgroupOf.mpr hk)

private theorem exists_wAction_eq_of_mem_closure {A B : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (D : Set G)) (hBN : B ≤ Subgroup.normalizer (D : Set G))
    {a₀ b₀ : G} (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ B) {z : V ≃ₗ[ZMod 3] V}
    (hz : z ∈ Subgroup.closure
      ({Sec12.wAction f ⟨a₀, hAN ha₀⟩, Sec12.wAction f ⟨b₀, hBN hb₀⟩} :
        Set (V ≃ₗ[ZMod 3] V))) :
    ∃ n : Subgroup.normalizer (D : Set G), (n : G) ∈ A ⊔ B ∧ Sec12.wAction f n = z := by
  have hle : Subgroup.closure
      ({Sec12.wAction f ⟨a₀, hAN ha₀⟩, Sec12.wAction f ⟨b₀, hBN hb₀⟩} :
        Set (V ≃ₗ[ZMod 3] V)) ≤
      ((A ⊔ B).comap (Subgroup.normalizer (D : Set G)).subtype).map (Sec12.wAction f) := by
    rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact ⟨⟨a₀, hAN ha₀⟩, show a₀ ∈ A ⊔ B from Subgroup.mem_sup_left ha₀, rfl⟩
    · exact ⟨⟨b₀, hBN hb₀⟩, show b₀ ∈ A ⊔ B from Subgroup.mem_sup_right hb₀, rfl⟩
  obtain ⟨n, hn, hnz⟩ := hle hz
  exact ⟨n, hn, hnz⟩

end Aux

private theorem exists_mem_normalizer_of_conj_le {A K : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAK : A ≤ K)
    (hwc : ∀ R : Subgroup G, IsPGroup 3 R → A ≤ R → ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ R → A.map (MulAut.conj g).toMonoidHom = A)
    {g : G} (hg : A.map (MulAut.conj g).toMonoidHom ≤ K) :
    ∃ m ∈ K, m⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS, hAS⟩ := exists_isSylowOf_ge hAK hA3
  obtain ⟨m, hmK, hm⟩ := exists_conj_le_of_isSylowOf hS hg (hA3.map _)
  refine ⟨m, hmK, ?_⟩
  have hle : A.map (MulAut.conj (m⁻¹ * g)).toMonoidHom ≤ S := by
    rintro _ ⟨a, ha, rfl⟩
    have h := hm _ (Subgroup.mem_map_of_mem _ ha)
    simpa [MulAut.conj_apply, mul_assoc] using h
  have heq := hwc S hS.isPGroup hAS (m⁻¹ * g) hle
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : (m⁻¹ * g) * h * (m⁻¹ * g)⁻¹ ∈ A.map (MulAut.conj (m⁻¹ * g)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hh
    rwa [heq] at h1
  · intro hh
    rw [← heq] at hh
    obtain ⟨a, ha, hae⟩ := hh
    have hah : a = h := mul_left_cancel (mul_right_cancel hae)
    rw [← hah]
    exact ha

private theorem card_eq_three_mul_card_inf_centralizer {E D : Subgroup G}
    (hE27 : Nat.card E = 27) (hED9 : Nat.card (E ⊓ D : Subgroup G) = 9)
    (hDC : D ≤ Subgroup.centralizer (D : Set G))
    (hnot : ¬ E ≤ Subgroup.centralizer (D : Set G)) :
    Nat.card E = 3 * Nat.card (E ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) := by
  set C := Subgroup.centralizer (D : Set G)
  have hdvd : Nat.card (E ⊓ C : Subgroup G) ∣ 27 := by
    rw [← hE27]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h9 : 9 ∣ Nat.card (E ⊓ C : Subgroup G) := by
    rw [← hED9]
    exact Subgroup.card_dvd_of_le (inf_le_inf_left E hDC)
  obtain ⟨k, hk⟩ := h9
  have hk3 : k ∣ 3 := by
    rw [hk] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by simpa using hdvd)
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
  · rw [hE27, hk]
  · exfalso
    apply hnot
    have h27 : Nat.card (E ⊓ C : Subgroup G) = Nat.card E := by rw [hk, hE27]
    have : E ⊓ C = E := Subgroup.eq_of_le_of_card_ge inf_le_left h27.ge
    exact inf_eq_left.mp this

section Transv

variable {D : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  (hV : Module.finrank (ZMod 3) V = 3) (f : Multiplicative V ≃* D)

include hV in
private theorem exists_transv {E : Subgroup G}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hEN : E ≤ Subgroup.normalizer (D : Set G)) (hED9 : Nat.card (E ⊓ D : Subgroup G) = 9)
    {e₀ : G} (he₀ : e₀ ∈ E) (he₀C : e₀ ∉ Subgroup.centralizer (D : Set G)) :
    ∃ (v : V) (α : Module.Dual (ZMod 3) V),
      CFSG.RankThree.Classical.IsTransvectionWith (Sec12.wAction f ⟨e₀, hEN he₀⟩) v α ∧
        ∀ (y : G) (hy : y ∈ D), y ∈ E ↔ α (Sec12.coordVec f ⟨y, hy⟩) = 0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  set t := Sec12.wAction f ⟨e₀, hEN he₀⟩ with ht
  have ht3 : t ^ 3 = 1 := by
    rw [ht, ← map_pow]
    have h : (⟨e₀, hEN he₀⟩ : Subgroup.normalizer (D : Set G)) ^ 3 = 1 :=
      Subtype.ext (hE3 e₀ he₀)
    rw [h, map_one]
  have ht1 : t ≠ 1 := fun h => he₀C ((wAction_eq_one_iff f ⟨e₀, hEN he₀⟩).mp h)
  have hfix : ∀ (y : G) (hy : y ∈ D), y ∈ E →
      t (Sec12.coordVec f ⟨y, hy⟩) = Sec12.coordVec f ⟨y, hy⟩ := fun y hy hyE =>
    (wAction_coordVec_eq_iff f ⟨e₀, hEN he₀⟩ hy).mpr (hEc e₀ he₀ y hyE)
  let ι : ↥(E ⊓ D : Subgroup G) → LinearMap.ker ((t : V →ₗ[ZMod 3] V) - 1) :=
    fun y => ⟨Sec12.coordVec f ⟨y.1, (Subgroup.mem_inf.mp y.2).2⟩, by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
        hfix y.1 (Subgroup.mem_inf.mp y.2).2 (Subgroup.mem_inf.mp y.2).1, sub_self]⟩
  have hι : Function.Injective ι := by
    intro y y' h
    apply Subtype.ext
    exact eq_of_coordVec_eq f (Subgroup.mem_inf.mp y.2).2 (Subgroup.mem_inf.mp y'.2).2
      (congrArg Subtype.val h)
  have h9 : 9 ≤ Nat.card (LinearMap.ker ((t : V →ₗ[ZMod 3] V) - 1)) :=
    hED9 ▸ Nat.card_le_card_of_injective ι hι
  obtain ⟨v, α, hα⟩ := exists_isTransvectionWith_of_card_le hV ht3 ht1 h9
  have hfwd : ∀ (y : G) (hy : y ∈ D), y ∈ E → α (Sec12.coordVec f ⟨y, hy⟩) = 0 := by
    intro y hy hyE
    have h1 := hα.2.2.2 (Sec12.coordVec f ⟨y, hy⟩)
    rw [hfix y hy hyE] at h1
    have h2 : α (Sec12.coordVec f ⟨y, hy⟩) • v = 0 := by
      have h3 : Sec12.coordVec f ⟨y, hy⟩ + 0 =
          Sec12.coordVec f ⟨y, hy⟩ + α (Sec12.coordVec f ⟨y, hy⟩) • v := by
        rw [add_zero]
        exact h1
      exact (add_left_cancel h3).symm
    exact (smul_eq_zero.mp h2).resolve_right hα.1
  refine ⟨v, α, hα, fun y hy => ⟨fun hyE => hfwd y hy hyE, fun hy0 => ?_⟩⟩
  have hkerα : Nat.card (LinearMap.ker α) ≤ 9 := by
    have hne : LinearMap.ker α ≠ ⊤ := fun h => hα.2.1 (LinearMap.ker_eq_top.mp h)
    have hlt := Submodule.finrank_lt hne
    rw [hV] at hlt
    rw [← FiniteField.pow_finrank_eq_natCard 3 (LinearMap.ker α)]
    calc 3 ^ Module.finrank (ZMod 3) (LinearMap.ker α) ≤ 3 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  let ι' : ↥(E ⊓ D : Subgroup G) → LinearMap.ker α :=
    fun y => ⟨Sec12.coordVec f ⟨y.1, (Subgroup.mem_inf.mp y.2).2⟩, by
      rw [LinearMap.mem_ker]
      exact hfwd y.1 (Subgroup.mem_inf.mp y.2).2 (Subgroup.mem_inf.mp y.2).1⟩
  have hι' : Function.Injective ι' := by
    intro y y' h
    apply Subtype.ext
    exact eq_of_coordVec_eq f (Subgroup.mem_inf.mp y.2).2 (Subgroup.mem_inf.mp y'.2).2
      (congrArg Subtype.val h)
  have hbij : Function.Bijective ι' := hι'.bijective_of_nat_card_le (by rw [hED9]; exact hkerα)
  obtain ⟨y', hy'⟩ := hbij.2 ⟨Sec12.coordVec f ⟨y, hy⟩, LinearMap.mem_ker.mpr hy0⟩
  have h1 : Sec12.coordVec f ⟨y'.1, (Subgroup.mem_inf.mp y'.2).2⟩ =
      Sec12.coordVec f ⟨y, hy⟩ := congrArg Subtype.val hy'
  have h2 : y'.1 = y := eq_of_coordVec_eq f _ hy h1
  rw [← h2]
  exact (Subgroup.mem_inf.mp y'.2).1

end Transv

private theorem exists_conj_data {A B : Subgroup G} {c d x : G} (hA3 : IsPGroup 3 A)
    (hB : B = A.map (MulAut.conj x).toMonoidHom) (hd : d = x * c * x⁻¹)
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hwc : ∀ R : Subgroup G, IsPGroup 3 R → A ≤ R → ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ R → A.map (MulAut.conj g).toMonoidHom = A) :
    ∃ k ∈ A ⊔ B, (∃ j : ℤ, k⁻¹ * d * k = c ^ j) ∧ ∃ i : ℤ, k * c * k⁻¹ = d ^ i := by
  obtain ⟨k, hk, hkn⟩ := exists_mem_normalizer_of_conj_le (K := A ⊔ B) hA3 le_sup_left hwc
    (g := x) (by rw [← hB]; exact le_sup_right)
  have hn := hWc hkn
  refine ⟨k, hk, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hn c).mp (Subgroup.mem_zpowers c))
    refine ⟨j, ?_⟩
    rw [hj, hd]
    group
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp (inv_mem hn) c).mp (Subgroup.mem_zpowers c))
    refine ⟨i, ?_⟩
    rw [hd, conj_zpow, hi]
    group

section Main

variable {D : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  (hV : Module.finrank (ZMod 3) V = 3) (f : Multiplicative V ≃* D)

include hV f in
private theorem false_of_transvection_pair_aux {A B : Subgroup G} {c d x : G}
    (hD : CFSG.Open.IsElemAbelian 3 D) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hAD9 : Nat.card (A ⊓ D : Subgroup G) = 9) (hBD9 : Nat.card (B ⊓ D : Subgroup G) = 9)
    (hB : B = A.map (MulAut.conj x).toMonoidHom) (hd : d = x * c * x⁻¹)
    (hcA : c ∈ A) (hcD : c ∈ D) (hdD : d ∈ D) (hcB : c ∉ B) (hdA : d ∉ A)
    (hself : ∀ y : G, y ^ 3 = 1 → (∀ a ∈ A, a * y = y * a) → y ∈ A)
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hwc : ∀ R : Subgroup G, IsPGroup 3 R → A ≤ R → ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ R → A.map (MulAut.conj g).toMonoidHom = A)
    (hcomm : ∀ a ∈ A, ∀ e ∈ D, a * e * a⁻¹ * e⁻¹ ≠ c) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hDc : ∀ y ∈ D, ∀ z ∈ D, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hDC : D ≤ Subgroup.centralizer (D : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => hDc z hz y hy
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA27]; norm_num)
  have hB27 : Nat.card B = 27 := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj x).injective, hA27]
  have hBmem : ∀ b ∈ B, ∃ a ∈ A, b = x * a * x⁻¹ := by
    intro b hb
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, ha, rfl⟩
  have hxB : ∀ a ∈ A, x * a * x⁻¹ ∈ B := fun a ha => by
    rw [hB]
    exact ⟨a, ha, rfl⟩
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨a, ha, rfl⟩ := hBmem b hb
    obtain ⟨a', ha', rfl⟩ := hBmem b' hb'
    calc x * a * x⁻¹ * (x * a' * x⁻¹) = x * (a * a') * x⁻¹ := by group
      _ = x * (a' * a) * x⁻¹ := by rw [hAc a ha a' ha']
      _ = x * a' * x⁻¹ * (x * a * x⁻¹) := by group
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBmem b hb
    rw [conj_pow, hA.2 a ha]
    group
  have hselfB : ∀ y : G, y ^ 3 = 1 → (∀ b ∈ B, b * y = y * b) → y ∈ B := by
    intro y hy3 hyc
    have hxy : x⁻¹ * y * x ∈ A := by
      refine hself _ ?_ ?_
      · have h : (x⁻¹ * y * x) ^ 3 = x⁻¹ * y ^ 3 * x := by
          have := conj_pow (a := x⁻¹) (b := y) (i := 3)
          rwa [inv_inv] at this
        rw [h, hy3]
        group
      · intro a ha
        have h := hyc (x * a * x⁻¹) (hxB a ha)
        calc a * (x⁻¹ * y * x) = x⁻¹ * ((x * a * x⁻¹) * y) * x := by group
          _ = x⁻¹ * (y * (x * a * x⁻¹)) * x := by rw [h]
          _ = x⁻¹ * y * x * a := by group
    have h := hxB _ hxy
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h
  have hdB : d ∈ B := by
    rw [hd]
    exact hxB c hcA
  have hAnC : ¬ A ≤ Subgroup.centralizer (D : Set G) := by
    intro hAC
    exact hdA (hself d (hD.2 d hdD) fun a ha =>
      ((Subgroup.mem_centralizer_iff.mp (hAC ha)) d hdD).symm)
  have hBnC : ¬ B ≤ Subgroup.centralizer (D : Set G) := by
    intro hBC
    exact hcB (hselfB c (hD.2 c hcD) fun b hb =>
      ((Subgroup.mem_centralizer_iff.mp (hBC hb)) c hcD).symm)
  have hAcard := card_eq_three_mul_card_inf_centralizer hA27 hAD9 hDC hAnC
  have hBcard := card_eq_three_mul_card_inf_centralizer hB27 hBD9 hDC hBnC
  obtain ⟨a₀, ha₀, ha₀C⟩ : ∃ a₀ ∈ A, a₀ ∉ Subgroup.centralizer (D : Set G) := by
    by_contra! h
    exact hAnC h
  obtain ⟨b₀, hb₀, hb₀C⟩ : ∃ b₀ ∈ B, b₀ ∉ Subgroup.centralizer (D : Set G) := by
    by_contra! h
    exact hBnC h
  obtain ⟨v, α, h₁, hα⟩ := exists_transv hV f hAc hA.2 hAD hAD9 ha₀ ha₀C
  obtain ⟨w, β, h₂, hβ⟩ := exists_transv hV f hBc hB3 hBD hBD9 hb₀ hb₀C
  have hαc : α (Sec12.coordVec f ⟨c, hcD⟩) = 0 := (hα c hcD).mp hcA
  have hαd : α (Sec12.coordVec f ⟨d, hdD⟩) ≠ 0 := fun h => hdA ((hα d hdD).mpr h)
  have hβd : β (Sec12.coordVec f ⟨d, hdD⟩) = 0 := (hβ d hdD).mp hdB
  have hβc : β (Sec12.coordVec f ⟨c, hcD⟩) ≠ 0 := fun h => hcB ((hβ c hcD).mpr h)
  have hAB : A ⊔ B ≤ Subgroup.normalizer (D : Set G) := sup_le hAD hBD
  have hρA : ∀ (a : G) (ha : a ∈ A), Sec12.wAction f ⟨a, hAD ha⟩ ∈
      Subgroup.zpowers (Sec12.wAction f ⟨a₀, hAD ha₀⟩) := fun a ha =>
    wAction_mem_zpowers f hAD hAcard ha₀ ha₀C ha
  have hρB : ∀ (b : G) (hb : b ∈ B), Sec12.wAction f ⟨b, hBD hb⟩ ∈
      Subgroup.zpowers (Sec12.wAction f ⟨b₀, hBD hb₀⟩) := fun b hb =>
    wAction_mem_zpowers f hBD hBcard hb₀ hb₀C hb
  have hclos : ∀ {k : G} (hk : k ∈ A ⊔ B), Sec12.wAction f ⟨k, hAB hk⟩ ∈
      Subgroup.closure ({Sec12.wAction f ⟨a₀, hAD ha₀⟩, Sec12.wAction f ⟨b₀, hBD hb₀⟩} :
        Set (V ≃ₗ[ZMod 3] V)) := by
    intro k hk
    refine wAction_mem_of_mem_sup f hAD hBD _ (fun a ha => ?_) (fun b hb => ?_) hk
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) (hρA a ha)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) (hρB b hb)
  obtain ⟨k, hkAB, ⟨j, hj⟩, ⟨i, hi⟩⟩ := exists_conj_data hA3 hB hd hWc hwc
  have hκ := hclos hkAB
  have hκ' := hclos (inv_mem hkAB)
  by_cases hβv : β v = 0
  · have h1 := apply_eq_of_mem_closure_pair h₁ h₂ hβv h₂.2.2.1 hκ (Sec12.coordVec f ⟨c, hcD⟩)
    have h2 := wAction_coordVec_zpow f ⟨k, hAB hkAB⟩ hcD hdD hi
    rw [h2, map_smul, hβd, smul_zero] at h1
    exact hβc h1.symm
  by_cases hαw : α w = 0
  · have h1 := apply_eq_of_mem_closure_pair h₁ h₂ h₁.2.2.1 hαw hκ' (Sec12.coordVec f ⟨d, hdD⟩)
    have h2 := wAction_coordVec_zpow f ⟨k⁻¹, hAB (inv_mem hkAB)⟩ hdD hcD (i := j)
      (by show k⁻¹ * d * k⁻¹⁻¹ = c ^ j; rw [inv_inv]; exact hj)
    rw [h2, map_smul, hαc, smul_zero] at h1
    exact hαd h1.symm
  obtain ⟨z, hzcl, hzP, hzL⟩ := Sec3.exists_neg_mem_pair h₁ h₂ hαw hβv hV
  obtain ⟨n, hnAB, hnz⟩ := exists_wAction_eq_of_mem_closure f hAD hBD ha₀ hb₀ hzcl
  have hzt : z * Sec12.wAction f ⟨a₀, hAD ha₀⟩ = Sec12.wAction f ⟨a₀, hAD ha₀⟩ * z :=
    mul_comm_of_neg_pair h₁ h₂ hαw hβv hzP hzL
  have hcomm_n : ∀ (a : G) (ha : a ∈ A),
      (n : G) * a * (n : G)⁻¹ * a⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    intro a ha
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hρA a ha)
    have hcz : z * Sec12.wAction f ⟨a, hAD ha⟩ = Sec12.wAction f ⟨a, hAD ha⟩ * z := by
      rw [← hm]
      exact (Commute.zpow_right
        (show Commute z (Sec12.wAction f ⟨a₀, hAD ha₀⟩) from hzt) m).eq
    have hone : Sec12.wAction f (n * (⟨a, hAD ha⟩ : Subgroup.normalizer (D : Set G)) * n⁻¹ *
        (⟨a, hAD ha⟩ : Subgroup.normalizer (D : Set G))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hnz, hcz]
      group
    exact (wAction_eq_one_iff f _).mp hone
  have hAmap : A.map (MulAut.conj (n : G)).toMonoidHom ≤
      A ⊔ Subgroup.centralizer (D : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hcomm_n a ha
    have h2 : (MulAut.conj (n : G)).toMonoidHom a = ((n : G) * a * (n : G)⁻¹ * a⁻¹) * a := by
      simp [MulAut.conj_apply]
    rw [h2, sup_comm]
    exact Subgroup.mul_mem_sup h1 ha
  obtain ⟨m, hmK, hm⟩ := exists_mem_normalizer_of_conj_le hA3 le_sup_left hwc hAmap
  have hCN : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hmN : m ∈ Subgroup.normalizer (D : Set G) := sup_le hAD hCN hmK
  have hτ : Sec12.wAction f ⟨m, hmN⟩ ∈ Subgroup.zpowers (Sec12.wAction f ⟨a₀, hAD ha₀⟩) := by
    refine wAction_mem_of_mem_sup f hAD hCN _ hρA (fun y hy => ?_) hmK
    rw [(wAction_eq_one_iff f ⟨y, hCN hy⟩).mpr hy]
    exact one_mem _
  obtain ⟨μ, hμ⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp (hWc hm) c).mp (Subgroup.mem_zpowers c))
  have hkey := wAction_coordVec_zpow f
    ((⟨m, hmN⟩ : Subgroup.normalizer (D : Set G))⁻¹ * n) hcD hcD hμ.symm
  rw [map_mul, map_inv, hnz] at hkey
  have hu := mem_span_of_eigen h₁ h₂ hαw hβv hzP hzL (inv_mem hτ) hαc hβc hkey
  obtain ⟨y, hy⟩ := exists_eq_sub_of_mem_span h₁ hu
  obtain ⟨e, he, rfl⟩ := exists_coordVec_eq f y
  have hae : a₀ * e * a₀⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hAD ha₀) e).mp he
  have h3 : Sec12.wAction f ⟨a₀, hAD ha₀⟩ (Sec12.coordVec f ⟨e, he⟩) =
      Sec12.coordVec f ⟨a₀ * e * a₀⁻¹, hae⟩ := wAction_coordVec f ⟨a₀, hAD ha₀⟩ he
  have h4 : Sec12.coordVec f ⟨c, hcD⟩ =
      Sec12.coordVec f ⟨a₀ * e * a₀⁻¹ * e⁻¹, D.mul_mem hae (D.inv_mem he)⟩ := by
    rw [coordVec_mul f hae (D.inv_mem he), coordVec_inv f he, ← sub_eq_add_neg, ← h3]
    exact hy
  exact hcomm a₀ ha₀ e he (eq_of_coordVec_eq f hcD _ h4).symm

end Main

private instance instModuleFinThree :
    @Module (ZMod 3) (Fin 3 → ZMod 3) _ AddCommGroup.toAddCommMonoid :=
  Pi.module _ _ _

theorem false_of_transvection_pair {A B D : Subgroup G} {c d x : G}
    (hD : CFSG.Open.IsElemAbelian 3 D) (hD27 : Nat.card D = 27)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hAD9 : Nat.card (A ⊓ D : Subgroup G) = 9) (hBD9 : Nat.card (B ⊓ D : Subgroup G) = 9)
    (hB : B = A.map (MulAut.conj x).toMonoidHom) (hd : d = x * c * x⁻¹)
    (hcA : c ∈ A) (hcD : c ∈ D) (hdD : d ∈ D) (hcB : c ∉ B) (hdA : d ∉ A)
    (hself : ∀ y : G, y ^ 3 = 1 → (∀ a ∈ A, a * y = y * a) → y ∈ A)
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hwc : ∀ R : Subgroup G, IsPGroup 3 R → A ≤ R → ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ≤ R → A.map (MulAut.conj g).toMonoidHom = A)
    (hcomm : ∀ a ∈ A, ∀ e ∈ D, a * e * a⁻¹ * e⁻¹ ≠ c) : False := by
  obtain ⟨f⟩ := Sec12.exists_coords hD (show Nat.card D = 3 ^ 3 by rw [hD27]; norm_num)
  exact false_of_transvection_pair_aux (Module.finrank_fin_fun (ZMod 3)) f hD hA hA27 hAD hBD
    hAD9 hBD9 hB hd hcA hcD hdD hcB hdA hself hWc hwc hcomm

end CFSG.RankThree.PartTwo.Sec18.Item1810Proof
