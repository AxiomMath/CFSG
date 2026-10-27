module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419Gen
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419

open CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits

theorem hasTwoWitness_of_fixLine
    {s : titsD} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) {p : Fin 2925} (hp : titsDLineAct s p = p) :
    HasTwoWitness s := by
  obtain ⟨k, hk⟩ := titsDLine_transitive p
  have hn : k⁻¹ * s * k ∈ titsLineStab := by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, map_mul, map_mul, map_inv,
      Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hk, hp, ← hk]
    simp
  have hnN : k⁻¹ * s * k ∈ titsN.subgroupOf titsD := by
    rw [Subgroup.mem_subgroupOf, titsN_eq_stab]
    exact ⟨_, hn, rfl⟩
  have hn3 : (k⁻¹ * s * k) ^ 3 = 1 := by
    rw [show k⁻¹ * s * k = k⁻¹ * s * k⁻¹⁻¹ by rw [inv_inv], conj_pow, hs3, mul_one,
      mul_inv_cancel]
  have hn1 : k⁻¹ * s * k ≠ 1 := by
    intro h
    apply hs1
    calc s = k * (k⁻¹ * s * k) * k⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨-, -, hNK, -, -, hK2, -, -, -, -, -, hCK⟩ := AT_Tits_intrinsic_local_pair
  have hQ2 : IsPGroup 2 (titsK.subgroupOf titsD) :=
    hK2.of_equiv (Subgroup.subgroupOfEquivOfLe titsK_le_titsD).symm
  have hnorm : ∀ a ∈ titsN.subgroupOf titsD, ∀ q ∈ titsK.subgroupOf titsD,
      a * q * a⁻¹ ∈ titsK.subgroupOf titsD := by
    intro a ha q hq
    have haN : (a : Equiv.Perm (Fin 1755)) ∈ titsD ⊓
        Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) := hNK ▸ ha
    exact (Subgroup.mem_normalizer_iff.mp haN.2 (q : Equiv.Perm (Fin 1755))).mp hq
  have hcen : ∀ a ∈ titsN.subgroupOf titsD,
      (∀ q ∈ titsK.subgroupOf titsD, a * q = q * a) → a ∈ titsK.subgroupOf titsD := by
    intro a ha hc
    have haC : (a : Equiv.Perm (Fin 1755)) ∈
        Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (congrArg Subtype.val (hc ⟨q, titsK_le_titsD hq⟩ hq)).symm
    exact hCK (show (a : Equiv.Perm (Fin 1755)) ∈ titsN ⊓
      Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) from ⟨ha, haC⟩)
  have hw : HasTwoWitness (k⁻¹ * s * k) :=
    hasTwoWitness_of_selfCentralizing hQ2 hnorm hcen hnN hn3 hn1
  exact hasTwoWitness_of_conj k (k⁻¹ * s * k) s (by group) hw

theorem hasTwoWitness_titsD
    {x : titsD} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    HasTwoWitness x := by
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨g, hg⟩ := exists_conj_mem_sylGrp hord
  generalize hs : g * x * g⁻¹ = s at hg
  have hs3 : s ^ 3 = 1 := by
    rw [← hs, conj_pow, hx3, mul_one, mul_inv_cancel]
  have hs1 : s ≠ 1 := by
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [hs, h]; group
  have hsP1 : (s : Equiv.Perm (Fin 1755)) ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨h5, -⟩ := lines_of_mem_sylGrp hg hsP1
  have hρs : titsDLineAct ⟨(s : Equiv.Perm (Fin 1755)), sylGrp_le_titsD hg⟩ = titsDLineAct s :=
    rfl
  rw [hρs] at h5
  have hpos : 0 < Fintype.card {p : Fin 2925 // titsDLineAct s p = p} :=
    Nat.pos_of_ne_zero fun h => h5 (h ▸ dvd_zero 5)
  obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hpos
  have hw : HasTwoWitness s := hasTwoWitness_of_fixLine hs3 hs1 hp
  exact hasTwoWitness_of_conj g⁻¹ s x (by rw [← hs]; group) hw

theorem hasTwoWitness_of_reeTitsModel
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.ReeTitsModel X .Tits 2 1) {k : X} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) :
    HasTwoWitness k := by
  obtain ⟨e⟩ := titsModelEquiv X 2 1 hX
  refine hasTwoWitness_of_mulEquiv e ?_
  exact hasTwoWitness_titsD (by rw [← map_pow, hk3, map_one])
    (fun h => hk1 (EmbeddingLike.map_eq_one_iff.mp h))

end CFSG.RankThree.PartTwo.Sec4.HeringK419
