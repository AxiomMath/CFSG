module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Abs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Arith
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3BT
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Four
import CFSG.RankThree.PartTwo.Sec12.Hering129GMod9Mat
import CFSG.RankThree.PartTwo.Sec12.Hering129LSL3
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

variable {f : ℕ} {K : Type} [Field K]

theorem false_of_inner_unitary (hK : Sec4.PiField false 2 f K) (hq : Sec4.ModThree false (2 ^ f))
    (hq2 : 2 < 2 ^ f) {c g : MulAut (Sec4.slPi false 3 (2 ^ f) K)}
    {V U : Subgroup (MulAut (Sec4.slPi false 3 (2 ^ f) K))} (h : Res3Datum c g V U)
    {j : Sec4.slPi false 3 (2 ^ f) K} (hj : MulAut.conj j = c) : False := by
  obtain ⟨hj3, hjz⟩ := h.inner_pow_three_of_conj hj
  have hVj : MulAut.conj j ∈ Subgroup.normalizer
      (V : Set (MulAut (Sec4.slPi false 3 (2 ^ f) K))) := by
    rw [hj]
    exact h.c_mem
  exact h.false_of_commutator_inf_eq_bot (commutator_le_range_slPiConj hK hq2)
    (inf_range_eq_bot_of_unitary hK hq hj3 hjz h.V_isPGroup hVj)

theorem false_of_cube_torus (hK : Sec4.PiField true 2 f K) (hq : Sec4.ModThree true (2 ^ f))
    (h9 : 9 ∣ 2 ^ f - 1) {j : Sec4.slPi true 3 (2 ^ f) K} (hj3 : j ^ 3 = 1)
    (hjz : j ∉ Subgroup.center (Sec4.slPi true 3 (2 ^ f) K))
    (hcube : ∀ x : Sec4.slPi true 3 (2 ^ f) K, MulAut.conj j x = x →
      x ^ 3 ∈ Subgroup.center (Sec4.slPi true 3 (2 ^ f) K) → x ^ 3 = 1) : False := by
  obtain ⟨δ, σ, -, z, hz, hz1, -, hδ, hσ3, hσz, -, hσδ, -⟩ :=
    Sec12.Hering129G.exists_data_slPi hK h9
  obtain ⟨g, hg⟩ := Sec12.Hering129L.exists_conj_of_pow_three_slPi hK hq hσ3 hj3 hσz hjz
  have hcomm : MulAut.conj j (g * δ * g⁻¹) = g * δ * g⁻¹ := by
    rw [MulAut.conj_apply, ← hg]
    have hσδ' : σ * δ * σ⁻¹ = δ := by rw [hσδ, mul_inv_cancel_right]
    calc g * σ * g⁻¹ * (g * δ * g⁻¹) * (g * σ * g⁻¹)⁻¹ = g * (σ * δ * σ⁻¹) * g⁻¹ := by group
      _ = g * δ * g⁻¹ := by rw [hσδ']
  have hcube3 : (g * δ * g⁻¹) ^ 3 = z := by
    rw [conj_pow, hδ, Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
  refine hz1 ?_
  rw [← hcube3]
  exact hcube _ hcomm (by rw [hcube3]; exact hz)

private noncomputable def fiveTorus (K : Type) [Field K] : Subgroup (GL (Fin 3) K) :=
  ((rootsOfUnity 5 K).prod (rootsOfUnity 5 K)).map Sec4.torusHom

private theorem fiveTorus_le (hK : Sec4.PiField true 2 f K) (h5 : 5 ∣ 2 ^ f - 1) :
    fiveTorus K ≤ Sec4.slPi true 3 (2 ^ f) K := by
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  exact Sec4.torusHom_mem_slPi hK (rootsOfUnity_le_of_dvd h5 ha) (rootsOfUnity_le_of_dvd h5 hb)

private theorem card_fiveTorus [Finite K] (h5 : 5 ∣ Nat.card K - 1) :
    Nat.card (fiveTorus K) = 25 := by
  haveI : NeZero 5 := ⟨by norm_num⟩
  rw [fiveTorus, Subgroup.card_map_of_injective Sec4.torusHom_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd h5]

private theorem pow_five_of_mem_fiveTorus {x : GL (Fin 3) K} (hx : x ∈ fiveTorus K) :
    x ^ 5 = 1 := by
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
  rw [← map_pow]
  have h : ((a, b) : Kˣ × Kˣ) ^ 5 = 1 :=
    Prod.ext ((mem_rootsOfUnity _ _).mp ha) ((mem_rootsOfUnity _ _).mp hb)
  rw [h, map_one]

private theorem offDiag_of_mem_fiveTorus {x : GL (Fin 3) K} (hx : x ∈ fiveTorus K)
    {i j : Fin 3} (hij : i ≠ j) : (x : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  obtain ⟨⟨a, b⟩, -, rfl⟩ := hx
  rw [Sec4.coe_torusHom, Matrix.diagonal_apply_ne _ hij]

theorem false_of_five_torus (hK : Sec4.PiField true 2 f K) (h5 : 5 ∣ 2 ^ f - 1)
    (hrank5 : ∀ E R : Subgroup (Sec4.slPi true 3 (2 ^ f) K), Nat.card E = 25 →
      (∀ x ∈ E, x ^ 5 = 1) → IsPGroup 2 R → R ≠ ⊥ →
      E ≤ Subgroup.normalizer (R : Set (Sec4.slPi true 3 (2 ^ f) K)) → False) : False := by
  haveI := hK.finite
  haveI := hK.charP
  have hle := fiveTorus_le hK h5
  have hRle : Sec4.rootGL K ≤ Sec4.slPi true 3 (2 ^ f) K := Sec4.rootGL_le_slPi _
  refine hrank5 ((fiveTorus K).subgroupOf _) ((Sec4.rootGL K).subgroupOf _) ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact card_fiveTorus (by rw [hK.card]; exact h5)
  · intro x hx
    exact Subtype.ext (by simpa using pow_five_of_mem_fiveTorus (Subgroup.mem_subgroupOf.mp hx))
  · refine IsPGroup.of_equiv ?_ (Subgroup.subgroupOfEquivOfLe hRle).symm
    intro M
    exact ⟨1, Subtype.ext (by simpa using Sec4.rootGL_sq M.2)⟩
  · intro hbot
    obtain ⟨⟨M, hM⟩, hM1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Sec4.rootGL_ne_bot (K := K))
    have hmem : (⟨M, hRle hM⟩ : ↥(Sec4.slPi true 3 (2 ^ f) K)) ∈
        (Sec4.rootGL K).subgroupOf (Sec4.slPi true 3 (2 ^ f) K) := hM
    rw [hbot, Subgroup.mem_bot] at hmem
    have hM' : M = 1 := congrArg Subtype.val hmem
    exact hM1 (Subtype.ext hM')
  · intro x hx
    apply Sec4.mem_normalizer_of_conj_mem
    intro y hy
    have hx' := Subgroup.mem_subgroupOf.mp hx
    have hD := fun i j (hij : i ≠ j) => offDiag_of_mem_fiveTorus hx' hij
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simpa using Sec4.conj_mem_rootGL_of_diag hD hy

theorem false_of_prime_torus (hK : Sec4.PiField true 2 f K) (hq : Sec4.ModThree true (2 ^ f))
    {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (hpd : p ∣ 2 ^ f - 1)
    {j : Sec4.slPi true 3 (2 ^ f) K} (hj3 : j ^ 3 = 1)
    (hjz : j ∉ Subgroup.center (Sec4.slPi true 3 (2 ^ f) K))
    (hprimes : ∀ x : Sec4.slPi true 3 (2 ^ f) K, MulAut.conj j x = x → (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hjs : (j : GL (Fin 3) K) ∉ CFSG.Open.StatedScalars (Fin 3) K := fun hs =>
    hjz (Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Sec4.commute_of_mem_statedScalars hs (g : GL (Fin 3) K)))
  have hj3' : (j : GL (Fin 3) K) ^ 3 ∈ CFSG.Open.StatedScalars (Fin 3) K := by
    rw [← Subgroup.coe_pow, hj3, Subgroup.coe_one]
    exact Subgroup.one_mem _
  obtain ⟨u, hu, hup, hu1, huc⟩ := KS1424.exists_centralizing_pElement hK hq hp hpd j.2 hjs hj3'
    (S := {(j : GL (Fin 3) K)}) (fun e he => by rw [Set.mem_singleton_iff.mp he]; exact j.2)
    (fun e he => by rw [Set.mem_singleton_iff.mp he])
  have hxp : (⟨u, hu⟩ : Sec4.slPi true 3 (2 ^ f) K) ^ p = 1 := Subtype.ext (by simpa using hup)
  have hx1 : (⟨u, hu⟩ : Sec4.slPi true 3 (2 ^ f) K) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hxo : orderOf (⟨u, hu⟩ : Sec4.slPi true 3 (2 ^ f) K) = p := orderOf_eq_prime hxp hx1
  have hcomm : MulAut.conj j (⟨u, hu⟩ : Sec4.slPi true 3 (2 ^ f) K) = ⟨u, hu⟩ := by
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (huc _ (Set.mem_singleton _)).symm
  have := hprimes _ hcomm (by rw [hxo]; exact hp)
  omega

theorem false_of_inner_linear (hK : Sec4.PiField true 2 f K) (hq : Sec4.ModThree true (2 ^ f))
    {c g : MulAut (Sec4.slPi true 3 (2 ^ f) K)}
    {V U : Subgroup (MulAut (Sec4.slPi true 3 (2 ^ f) K))} (h : Res3Datum c g V U)
    {j : Sec4.slPi true 3 (2 ^ f) K} (hj : MulAut.conj j = c) : False := by
  obtain ⟨hj3, hjz⟩ := h.inner_pow_three_of_conj hj
  have hf : Even f := even_exponent_of_two_pow_mod_three_one hq
  have hf2 : 2 ≤ f := by
    obtain ⟨m, hm⟩ := hf
    have := hK.one_le
    omega
  rcases exists_dvd_or_prime_of_two_pow_sub_one hf hf2 with h9 | h5 | hf2' | ⟨p, hp, h11, hpd⟩
  · exact false_of_cube_torus hK hq h9 hj3 hjz fun x hx hx3 => h.cube x (hj ▸ hx) hx3
  · exact false_of_five_torus hK h5 h.rank5
  · subst hf2'
    obtain ⟨α, p, hp, hp5, hα, hcomm⟩ := h.exists_commuting_prime_order_aut
    exact false_of_prime_order_commute_conj_card_four hK hj3 hjz hp hp5 hα (hj ▸ hcomm)
  · exact false_of_prime_torus hK hq hp h11 hpd hj3 hjz fun x hx => h.primes x (hj ▸ hx)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
