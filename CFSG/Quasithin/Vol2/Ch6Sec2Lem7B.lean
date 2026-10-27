module

public import CFSG.Quasithin.Vol2.Ch6Hyperplane
public import CFSG.Quasithin.Vol2.Ch6Sec1ZS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped Matrix commutatorElement

theorem eq_one_of_mulVec_ch62 {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {g : Matrix.SpecialLinearGroup (Fin 2) F} {k : ℕ} (hk : g ^ 3 ^ k = 1) {v : Fin 2 → F}
    (hv : v ≠ 0) (hg : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : g = 1 := by
  have hgg : g * g = 1 := by
    have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact g.2
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0
    set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1
    set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0
    set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1
    have e0 : (a + d) * v 0 = 0 := by
      linear_combination (1 - d) * h0 + b * h1 + v 0 * hdet + v 0 * h2
    have e1 : (a + d) * v 1 = 0 := by
      linear_combination c * h0 + (1 - a) * h1 + v 1 * hdet + v 1 * h2
    have hs : a + d = 0 := by
      by_contra hs
      apply hv
      funext i
      fin_cases i
      · exact (mul_eq_zero.mp e0).resolve_left hs
      · exact (mul_eq_zero.mp e1).resolve_left hs
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero,
        not_false_eq_true]
    · linear_combination a * hs - hdet - h2
    · linear_combination b * hs
    · linear_combination c * hs
    · linear_combination d * hs - hdet - h2
  have h1 : g ^ 2 = 1 := by rw [sq]; exact hgg
  have h3 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h4 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left _ (by norm_num)
  have h5 : orderOf g ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h3 h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)

variable {G : Type} [Group G]

theorem exists_eq_commutator_of_free_ch62 [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {d : G} (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hfree : ∀ w ∈ V, d * w = w * d → w = 1) {v : G} (hv : v ∈ V) :
    ∃ w ∈ V, w * d * w⁻¹ * d⁻¹ = v := by
  have hmem : ∀ w ∈ V, w * d * w⁻¹ * d⁻¹ ∈ V := fun w hw => by
    have : d * w⁻¹ * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hdV _).mp (V.inv_mem hw)
    have h2 := V.mul_mem hw this
    simpa [mul_assoc] using h2
  let f : ↥V →* ↥V :=
    { toFun := fun w => ⟨(w : G) * d * (w : G)⁻¹ * d⁻¹, hmem w w.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x : G) * y * d * ((x : G) * y)⁻¹ * d⁻¹ =
          ((x : G) * d * (x : G)⁻¹ * d⁻¹) * ((y : G) * d * (y : G)⁻¹ * d⁻¹)
        have ha : d * (x : G)⁻¹ * d⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp hdV _).mp (V.inv_mem x.2)
        have hb : d * (y : G)⁻¹ * d⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp hdV _).mp (V.inv_mem y.2)
        have hab := B2F.isElemAbelian_comm hV hb ha
        have hya := B2F.isElemAbelian_comm hV y.2 ha
        calc (x : G) * y * d * ((x : G) * y)⁻¹ * d⁻¹ =
              (x : G) * y * ((d * (y : G)⁻¹ * d⁻¹) * (d * (x : G)⁻¹ * d⁻¹)) := by group
          _ = (x : G) * y * ((d * (x : G)⁻¹ * d⁻¹) * (d * (y : G)⁻¹ * d⁻¹)) := by rw [hab]
          _ = (x : G) * ((y : G) * (d * (x : G)⁻¹ * d⁻¹)) * (d * (y : G)⁻¹ * d⁻¹) := by group
          _ = (x : G) * ((d * (x : G)⁻¹ * d⁻¹) * y) * (d * (y : G)⁻¹ * d⁻¹) := by rw [hya]
          _ = _ := by group }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hw' : (w : G) * d * (w : G)⁻¹ * d⁻¹ = 1 := congrArg Subtype.val hw
    have hdw : d * w = w * d := by
      have := congrArg (· * (d * w)) hw'
      simp only [one_mul] at this
      rw [← this]
      group
    exact Subtype.ext (hfree w w.2 hdw)
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨v, hv⟩
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem le_normalizer_of_commutator_le_ch62 [Finite G] {V U UH K D : Subgroup G}
    (hUH : IsElemAbelian 2 UH) (hVUH : V ≤ UH) (hUV : U ≤ V)
    (hKUH : K ≤ Subgroup.normalizer (UH : Set G)) {d : G} (hdD : d ∈ D)
    (hdUH : d ∈ Subgroup.normalizer (UH : Set G)) (hVd : ∀ v ∈ V, ∃ w ∈ V, w * d * w⁻¹ * d⁻¹ = v)
    (hKD : ∀ k ∈ K, ∀ d' ∈ D, k * d' * k⁻¹ * d'⁻¹ ∈
      centralizerMod U (Subgroup.normalizer (U : Set G)) UH)
    (hcomm : ⁅⁅UH, K⁆, D⁆ ≤ U) : K ≤ Subgroup.normalizer (V : Set G) := by
  have key : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
    intro k hk v hv
    obtain ⟨w, hwV, rfl⟩ := hVd v hv
    have hwUH := hVUH hwV
    have hkN := hKUH hk
    have hp : k * w * k⁻¹ ∈ UH := (Subgroup.mem_normalizer_iff.mp hkN w).mp hwUH
    have hq : d * w * d⁻¹ ∈ UH := (Subgroup.mem_normalizer_iff.mp hdUH w).mp hwUH
    have hr : d * (k * w * k⁻¹) * d⁻¹ ∈ UH := (Subgroup.mem_normalizer_iff.mp hdUH _).mp hp
    have hs : k * (d * w * d⁻¹) * k⁻¹ ∈ UH := (Subgroup.mem_normalizer_iff.mp hkN _).mp hq
    set p := k * w * k⁻¹ with hpdef
    set q := d * w * d⁻¹ with hqdef
    set r := d * p * d⁻¹ with hrdef
    set s := k * q * k⁻¹ with hsdef
    have hf : (k * d * k⁻¹ * d⁻¹) * r * (k * d * k⁻¹ * d⁻¹)⁻¹ * r⁻¹ ∈ U :=
      (mem_centralizerMod.mp (hKD k hk d hdD)).2.2 r hr
    have hcr : (k * d * k⁻¹ * d⁻¹) * r * (k * d * k⁻¹ * d⁻¹)⁻¹ = s := by
      rw [hrdef, hpdef, hsdef, hqdef]; group
    rw [hcr] at hf
    have he : ⁅⁅w, k⁆, d⁆ ∈ U :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hwUH hk) hdD)
    have he' : w * p⁻¹ * r * q⁻¹ ∈ U := by
      have e : ⁅⁅w, k⁆, d⁆ = w * p⁻¹ * r * q⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def, hrdef, hpdef, hqdef]; group
      rwa [e] at he
    have hc1 := B2F.isElemAbelian_comm hUH (UH.inv_mem hp) hr
    have hc2 := B2F.isElemAbelian_comm hUH hwUH hr
    have hc3 := B2F.isElemAbelian_comm hUH (UH.inv_mem hq) hs
    have hc4 := B2F.isElemAbelian_comm hUH hwUH hs
    have hc5 := B2F.isElemAbelian_comm hUH (UH.inv_mem hq) (UH.inv_mem hp)
    have hfe : (w * d * w⁻¹ * d⁻¹) * k * (w * d * w⁻¹ * d⁻¹)⁻¹ * k⁻¹ =
        (s * r⁻¹) * (w * p⁻¹ * r * q⁻¹) := by
      calc (w * d * w⁻¹ * d⁻¹) * k * (w * d * w⁻¹ * d⁻¹)⁻¹ * k⁻¹ = w * q⁻¹ * s * p⁻¹ := by
            rw [hsdef, hqdef, hpdef]; group
        _ = w * (q⁻¹ * s) * p⁻¹ := by group
        _ = w * (s * q⁻¹) * p⁻¹ := by rw [hc3]
        _ = (w * s) * (q⁻¹ * p⁻¹) := by group
        _ = (s * w) * (p⁻¹ * q⁻¹) := by rw [hc4, hc5]
        _ = s * r⁻¹ * (r * w) * p⁻¹ * q⁻¹ := by group
        _ = s * r⁻¹ * (w * r) * p⁻¹ * q⁻¹ := by rw [hc2]
        _ = s * r⁻¹ * w * (r * p⁻¹) * q⁻¹ := by group
        _ = s * r⁻¹ * w * (p⁻¹ * r) * q⁻¹ := by rw [hc1]
        _ = (s * r⁻¹) * (w * p⁻¹ * r * q⁻¹) := by group
    have hU : (w * d * w⁻¹ * d⁻¹) * k * (w * d * w⁻¹ * d⁻¹)⁻¹ * k⁻¹ ∈ U := by
      rw [hfe]; exact U.mul_mem hf he'
    have hvV : w * d * w⁻¹ * d⁻¹ ∈ V := hv
    have h1 : k * (w * d * w⁻¹ * d⁻¹)⁻¹ * k⁻¹ ∈ V := by
      have := V.mul_mem (V.inv_mem hvV) (hUV hU)
      simpa [mul_assoc] using this
    have h2 := V.inv_mem h1
    simpa [mul_assoc] using h2
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key k hk v, fun hv => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hv
  simpa [mul_assoc] using this

theorem card_sup_mul_card_inf_ch62 [Finite G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

namespace Hyp611Nat

theorem eq_one_of_commute_of_pow_three_ch62 [Finite G] {T M L V : Subgroup G} {n : ℕ}
    (h : Hyp611Nat G T M L V n) {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ Subgroup.centralizer (V : Set G)) {w : G} (hwV : w ∈ V) (hdw : d * w = w * d) :
    w = 1 := by
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  have h2 : (2 : h.data.K) = 0 := CharTwo.two_eq_zero
  set ℓ : ↥L := ⟨d, hdL⟩ with hℓ
  by_contra hw1
  have hE : Multiplicative.toAdd (h.data.E ⟨w, hwV⟩) ≠ 0 := by
    intro h0
    apply hw1
    have h3 : h.data.E ⟨w, hwV⟩ = h.data.E 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h0]; rfl)
    exact congrArg Subtype.val (h.data.E.injective h3)
  have hfix : ((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
      Matrix (Fin 2) (Fin 2) h.data.K) *ᵥ Multiplicative.toAdd (h.data.E ⟨w, hwV⟩) =
      Multiplicative.toAdd (h.data.E ⟨w, hwV⟩) := by
    rw [← h.data.conj_eq_rho, h.data.conj_apply]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    show d * w * d⁻¹ = w
    rw [hdw, mul_inv_cancel_right]
  have hρ3 : h.data.rho ℓ ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow]
    have : ℓ ^ 3 = 1 := Subtype.ext (by simpa [hℓ] using hd3)
    rw [this, map_one]
  have hρ1 := eq_one_of_mulVec_ch62 h2 hρ3 hE hfix
  exact hdC ((h.data.mem_ker_rho_iff ℓ).mp hρ1)

end Hyp611Nat

end CFSG.Quasithin.H13
