module

public import CFSG.Quasithin.Background.Harris.R1.NormGensL28
public import CFSG.Quasithin.Background.Harris.R1.NormGensL28Words

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)

omit [Fintype Ω] [DecidableEq Ω] in
include C in
theorem l28Prod_map_zeta {f ζ : Ω → G} (hf : ∀ ω, f ω ∈ vBeta K1 L2 S Zs)
    (hζ : ∀ ω, ζ ω ∈ Zs) (l : List Ω) :
    (l.map fun ω => ζ ω * f ω).prod = (l.map ζ).prod * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hP : (l.map ζ).prod ∈ Zs := Subgroup.list_prod_mem _ (fun x hx => by
      obtain ⟨ω, -, rfl⟩ := List.mem_map.1 hx
      exact hζ ω)
    have hc := C.Zs_central (hf a) hP
    simp only [List.map_cons, List.prod_cons, ih]
    calc ζ a * f a * ((l.map ζ).prod * (l.map f).prod)
        = ζ a * (f a * (l.map ζ).prod) * (l.map f).prod := by simp only [mul_assoc]
      _ = ζ a * ((l.map ζ).prod * f a) * (l.map f).prod := by rw [hc]
      _ = ζ a * (l.map ζ).prod * (f a * (l.map f).prod) := by simp only [mul_assoc]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem l28Prod_map_mul_left_comm {z : G} {f : Ω → G} (hf : ∀ ω, Commute z (f ω))
    (l : List Ω) :
    (l.map fun ω => z * f ω).prod = z ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih]
    have hc : Commute (f a) (z ^ l.length) := ((hf a).symm).pow_right _
    calc z * f a * (z ^ l.length * (l.map f).prod)
        = z * (f a * z ^ l.length) * (l.map f).prod := by simp only [mul_assoc]
      _ = z * (z ^ l.length * f a) * (l.map f).prod := by rw [hc.eq]
      _ = z ^ (l.length + 1) * (f a * (l.map f).prod) := by
        rw [pow_succ']
        simp only [mul_assoc]

omit [Finite G] in
theorem l28Prod_zpow_nine {z : G} (hz2 : z * z = 1) : z ^ 9 = z := by
  have h2 : z ^ 2 = 1 := by rw [sq]; exact hz2
  calc z ^ 9 = (z ^ 2) ^ 4 * z := by group
    _ = z := by rw [h2, one_pow, one_mul]

omit [Fintype Ω] [DecidableEq Ω] in
theorem coe_gprod_wU (l : List Ω) :
    ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G) = (l.map C.zf).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    rfl

theorem l28Prod_sign_mem_Zs {z : G} {σ : Ω → G} (hz : z ∈ Zs) (hσ : IsSignChoice C z σ)
    {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (hodd : Odd (Fintype.card Ω))
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (l : List Ω) (hl : l.Nodup) (hall : ∀ i, i ∈ l) : (l.map σ).prod ∈ Zs := by
  have hex : ∀ ω, ∃ ζ ∈ Zs, σ ω = ζ * C.zf ω := fun ω => IsSignChoice.exists_eq C hz hσ ω
  choose ζ hζ hσζ using hex
  have hσeq : l.map σ = l.map (fun ω => ζ ω * C.zf ω) :=
    List.map_congr_left (fun ω _ => hσζ ω)
  have hf : ∀ ω, C.zf ω ∈ vBeta K1 L2 S Zs := fun ω => C.zf_mem_U ω
  rw [hσeq, l28Prod_map_zeta C hf hζ l]
  refine Zs.mul_mem (Subgroup.list_prod_mem _ (fun x hx => ?_)) ?_
  · obtain ⟨ω, -, rfl⟩ := List.mem_map.1 hx
    exact hζ ω
  · have hg := FamCtxLemmas.gprod_univ_mem_Zs C hij hodd hcen l hl hall
    rw [coe_gprod_wU C l] at hg
    exact hg

omit [Fintype Ω] [DecidableEq Ω] in
theorem l28Prod_prod_conj {h9 : Fin 9 → G} {σ'' : Ω → G} (hK : ∀ i, h9 i ∈ K1)
    (hm : ∀ i, h9 i ∈ signStab C σ'') {ω : Fin 9 → Ω}
    (hω : ∀ i, ω i = C.D.act ⟨h9 i, hK i⟩ C.D.pt) :
    (List.ofFn fun i => h9 i * σ'' C.D.pt * (h9 i)⁻¹).prod =
      (List.ofFn fun i => σ'' (ω i)).prod := by
  have hfun : (fun i => h9 i * σ'' C.D.pt * (h9 i)⁻¹) = fun i => σ'' (ω i) := by
    funext i
    rw [hω i]
    obtain ⟨hk0, hk'⟩ := (mem_signStab_iff C σ'').1 (hm i)
    exact hk' C.D.pt
  rw [hfun]

theorem l28_sign_relator {z : G} {σ : Ω → G} (hz : z ∈ Zs) (hz1 : z ≠ 1)
    {i₀ j₀ : Ω} (hij₀ : i₀ ≠ j₀) (hzcm : z = C.cm i₀ j₀) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hcard : Fintype.card Ω = 9)
    (h9 : Fin 9 → G) (hK : ∀ i, h9 i ∈ K1) (hh : ∀ i, h9 i ∈ signStab C σ)
    (hcos : ∀ i j : Fin 9, i ≠ j → (h9 i)⁻¹ * h9 j ∉ borelOf K1 S) :
    ∃ σ' : Ω → G, IsSignChoice C z σ' ∧ signStab C σ' = signStab C σ ∧
      (List.ofFn fun i => h9 i * σ' C.D.pt * (h9 i)⁻¹).prod = z := by
  obtain ⟨ω, hω⟩ : ∃ ω : Fin 9 → Ω, ∀ i, ω i = C.D.act ⟨h9 i, hK i⟩ C.D.pt :=
    ⟨fun i => C.D.act ⟨h9 i, hK i⟩ C.D.pt, fun i => rfl⟩
  have hinj : Function.Injective ω := by
    intro i j hij
    by_contra hne
    apply hcos i j hne
    rw [hω i, hω j] at hij
    have hmem := C.D.mem_borelOf_of_pt_eq hij
    simpa using hmem
  have hbij : Function.Bijective ω :=
    (Fintype.bijective_iff_injective_and_card ω).2 ⟨hinj, by rw [Fintype.card_fin, hcard]⟩
  have hodd : Odd (Fintype.card Ω) := by rw [hcard]; exact ⟨4, rfl⟩
  have hall : ∀ x, x ∈ List.ofFn ω := by
    intro x
    obtain ⟨i, hi⟩ := hbij.2 x
    exact List.mem_ofFn.2 ⟨i, hi⟩
  have hP : (List.ofFn fun i => σ (ω i)).prod ∈ Zs := by
    have hl := l28Prod_sign_mem_Zs C hz hσ hij₀ hodd hcen (List.ofFn ω)
      (List.nodup_ofFn.2 hinj) hall
    rw [List.map_ofFn] at hl
    exact hl
  rcases Zs_cases C hz hz1 hP with hPone | hPz
  ·
    have hm' : ∀ i, h9 i ∈ signStab C (fun ω' => z * σ ω') := fun i => by
      rw [signStab_flip (σ := σ) C hz]
      exact hh i
    have hcomm : ∀ ω', Commute z (σ ω') := fun ω' =>
      (signRels_of_choice C hz hij₀ hzcm hσ).2.1 ω'
    have key : (List.ofFn fun i => z * σ (ω i)).prod = z ^ 9 * (List.ofFn fun i => σ (ω i)).prod := by
      have h := l28Prod_map_mul_left_comm hcomm (List.ofFn ω)
      rw [List.length_ofFn] at h
      simp only [List.map_ofFn] at h
      exact h
    refine ⟨fun ω' => z * σ ω', IsSignChoice.flip C hz hσ, signStab_flip (σ := σ) C hz, ?_⟩
    rw [l28Prod_prod_conj C hK hm' hω]
    show (List.ofFn fun i => z * σ (ω i)).prod = z
    rw [key, hPone, mul_one, l28Prod_zpow_nine (C.Zs_sq hz)]
  · refine ⟨σ, hσ, rfl, ?_⟩
    rw [l28Prod_prod_conj C hK hh hω]
    exact hPz

end CFSG.Quasithin.Background.Harris.R1

end
