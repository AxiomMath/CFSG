module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch3E213MP6EC

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6 CFSG.QuasithinUnique.A6Facts

variable {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal]

theorem card_le_two_of_dvd_ten {X : Type*} [Group X] [Finite X] {C : Subgroup X} (hC : IsPGroup 2 C)
    (h : Nat.card C ∣ 10) : Nat.card C ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hC.exists_card_eq
  rw [hk] at h ⊢
  have hk1 : k ≤ 1 := by
    by_contra hlt
    have h4 : 4 ∣ 10 := (Nat.pow_dvd_pow 2 (show 2 ≤ k by omega)).trans h
    omega
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num

theorem card_le_two_mul {D : Subgroup A} {v : A}
    (h : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ * v * d₁⁻¹ ≠ v → d₂ * v * d₂⁻¹ ≠ v →
      d₁ * v * d₁⁻¹ = d₂ * v * d₂⁻¹) :
    Nat.card D ≤ 2 * Nat.card ↥(D ⊓ Subgroup.centralizer ({v} : Set A)) := by
  classical
  set C := D ⊓ Subgroup.centralizer ({v} : Set A) with hCdef
  have hmemC : ∀ d ∈ D, d * v * d⁻¹ = v → d ∈ C := fun d hd hdv =>
    ⟨hd, Subgroup.mem_centralizer_singleton_iff.2 (by
      calc d * v = d * v * d⁻¹ * d := by group
        _ = v * d := by rw [hdv])⟩
  by_cases hex : ∃ d₁ ∈ D, d₁ * v * d₁⁻¹ ≠ v
  · obtain ⟨d₁, hd₁, hd₁v⟩ := hex
    have hcl : ∀ d ∈ D, d * v * d⁻¹ ≠ v → d₁⁻¹ * d ∈ C := by
      intro d hd hdv
      refine hmemC _ (D.mul_mem (D.inv_mem hd₁) hd) ?_
      have := h d₁ hd₁ d hd hd₁v hdv
      calc d₁⁻¹ * d * v * (d₁⁻¹ * d)⁻¹ = d₁⁻¹ * (d * v * d⁻¹) * d₁ := by group
        _ = d₁⁻¹ * (d₁ * v * d₁⁻¹) * d₁ := by rw [this]
        _ = v := by group
    let g : D → C × Bool := fun d =>
      if hd : (d : A) * v * (d : A)⁻¹ = v then (⟨d, hmemC _ d.2 hd⟩, false)
      else (⟨d₁⁻¹ * d, hcl _ d.2 hd⟩, true)
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g] at hab
      split_ifs at hab with ha hb hb
      · exact Subtype.ext (congrArg (fun p : C × Bool => (p.1 : A)) hab)
      · simp at hab
      · simp at hab
      · apply Subtype.ext
        have := congrArg (fun p : C × Bool => (p.1 : A)) hab
        simpa using this
    calc Nat.card D ≤ Nat.card (C × Bool) := Nat.card_le_card_of_injective g hg
      _ = 2 * Nat.card C := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
          Fintype.card_bool, mul_comm]
  · push Not at hex
    calc Nat.card D ≤ Nat.card C := Subgroup.card_le_of_le fun d hd => hmemC d hd (hex d hd)
      _ ≤ 2 * Nat.card C := Nat.le_mul_of_pos_left _ (by norm_num)

theorem mem_s6_of_mem {S E : Subgroup A} (hS2 : IsPGroup 2 S) (e : ↥K ≃* M6)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6)
    (hEK : ((E ⊓ K).subgroupOf K).map e.toMonoidHom ≤ Ra ⊓ Rb)
    (hSE : S ≤ Subgroup.normalizer (E : Set A)) (hE2 : ∀ x ∈ E, x * x = 1)
    (ι : A →* A6Models.autA6) (hι : Function.Injective ι)
    (hιK : ∀ k : K, ((ι k : A6Models.autA6) : P10) ∈ A6Models.psl29)
    {v : A} (hv : v ∈ E) : ((ι v : A6Models.autA6) : P10) ∈ s6 := by
  by_contra hns
  have hα2 : ((ι v : A6Models.autA6) : P10) * (ι v : A6Models.autA6) = 1 := by
    have h := congrArg (fun a : A6Models.autA6 => (a : P10)) (congrArg ι (hE2 v hv))
    simpa [map_mul] using h
  have hα1 : ((ι v : A6Models.autA6) : P10) ≠ 1 := fun h => hns (h ▸ s6.one_mem)
  have hαpsl : ((ι v : A6Models.autA6) : P10) ∉ A6Models.psl29 := fun h => hns (psl29_le_s6 h)
  have h10 := card_psl29_centralizer_of_not_mem (ι v).2 hα2 hα1 hαpsl hns
  set f : A →* P10 := A6Models.autA6.subtype.comp ι with hf
  have hfinj : Function.Injective f := Subtype.val_injective.comp hι
  have hCmap : ((S ⊓ K) ⊓ Subgroup.centralizer ({v} : Set A)).map f ≤
      A6Models.psl29 ⊓ Subgroup.centralizer ({((ι v : A6Models.autA6) : P10)} : Set P10) := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hc.2
    refine ⟨hιK ⟨c, hc.1.2⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    show (ι c : P10) * (ι v : P10) = (ι v : P10) * (ι c : P10)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h1]
  have hC2 : Nat.card ↥((S ⊓ K) ⊓ Subgroup.centralizer ({v} : Set A)) ≤ 2 := by
    refine card_le_two_of_dvd_ten (hS2.to_le (inf_le_left.trans inf_le_left)) ?_
    rw [← h10, ← Subgroup.card_map_of_injective hfinj]
    exact Subgroup.card_dvd_of_le hCmap
  have hD8 : Nat.card ↥(S ⊓ K) = 8 := by
    rw [← card_U6, ← he, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  have hval : ∀ d ∈ S ⊓ K, d * v * d⁻¹ ≠ v →
      ∃ hw : d * v * d⁻¹ * v⁻¹ ∈ K, ((e ⟨_, hw⟩ : M6) : P6) = zA := by
    intro d hd hdv
    have hwK : d * v * d⁻¹ * v⁻¹ ∈ K := by
      have h1 : v * d⁻¹ * v⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance _ (K.inv_mem hd.2) v
      have h2 := K.mul_mem hd.2 h1
      rwa [show d * (v * d⁻¹ * v⁻¹) = d * v * d⁻¹ * v⁻¹ by group] at h2
    have hwE : d * v * d⁻¹ * v⁻¹ ∈ E :=
      E.mul_mem ((Subgroup.mem_normalizer_iff.1 (hSE hd.1) v).1 hv) (E.inv_mem hv)
    have hmem : e ⟨_, hwK⟩ ∈ Ra ⊓ Rb := hEK ⟨⟨_, hwK⟩, ⟨hwE, hwK⟩, rfl⟩
    refine ⟨hwK, (mem_inf_VA_VB (x := ((e ⟨_, hwK⟩ : M6) : P6)) hmem).resolve_left fun h1 => ?_⟩
    apply hdv
    have h2 : e ⟨_, hwK⟩ = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    have h3 := congrArg Subtype.val h2
    simp only [OneMemClass.coe_one] at h3
    calc d * v * d⁻¹ = d * v * d⁻¹ * v⁻¹ * v := by group
      _ = v := by rw [h3, one_mul]
  have hcomm : ∀ d₁ ∈ S ⊓ K, ∀ d₂ ∈ S ⊓ K, d₁ * v * d₁⁻¹ ≠ v → d₂ * v * d₂⁻¹ ≠ v →
      d₁ * v * d₁⁻¹ = d₂ * v * d₂⁻¹ := by
    intro d₁ hd₁ d₂ hd₂ hn₁ hn₂
    obtain ⟨hw₁, h₁⟩ := hval d₁ hd₁ hn₁
    obtain ⟨hw₂, h₂⟩ := hval d₂ hd₂ hn₂
    have h3 : e ⟨_, hw₁⟩ = e ⟨_, hw₂⟩ := Subtype.ext (h₁.trans h₂.symm)
    have h4 := congrArg Subtype.val (e.injective h3)
    exact mul_right_cancel h4
  have := card_le_two_mul hcomm
  omega

end CFSG.Quasithin.Ch3E213M.P6E
