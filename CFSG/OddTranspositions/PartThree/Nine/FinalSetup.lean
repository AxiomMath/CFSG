module

public import CFSG.OddTranspositions.PartThree.Nine.Delta
public import CFSG.LargeExtraspecial.S111SHCor3
public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem card_regularCore_eq {Δ : Set G} {Q : Subgroup G} (hQ : IsRegularCore Δ Q) {u : G}
    (hu : u ∈ Δ) : Nat.card Q = Δ.ncard * Nat.card (Subgroup.centralizer Δ) := by
  classical
  obtain ⟨hQN, -, -, hCQ, htr, hreg⟩ := hQ
  let act : MulAction Q G :=
    { smul := fun x g => (x : G) * g * (x : G)⁻¹
      one_smul := fun g => by
        change ((1 : Q) : G) * g * ((1 : Q) : G)⁻¹ = g
        simp
      mul_smul := fun x y g => by
        change ((x * y : Q) : G) * g * ((x * y : Q) : G)⁻¹ =
          (x : G) * ((y : G) * g * (y : G)⁻¹) * (x : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group }
  have hsmul : ∀ (x : Q) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit Q u = Δ := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      change (x : G) * u * (x : G)⁻¹ ∈ Δ
      exact (hQN x.2 u).mp hu
    · intro hg
      obtain ⟨x, hx, hxg⟩ := htr u hu g hg
      exact ⟨⟨x, hx⟩, hxg⟩
  have hstab : (MulAction.stabilizer Q u).map Q.subtype = Subgroup.centralizer Δ := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hreg x x.2 u hu hx
    · intro hg
      refine ⟨⟨g, hCQ hg⟩, ?_, rfl⟩
      change g * u * g⁻¹ = u
      rw [(Subgroup.mem_centralizer_iff.mp hg u hu).symm, mul_inv_cancel_right]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer Q u)
  rw [MulAction.index_stabilizer, horb] at h1
  rw [← h1, ← hstab, Subgroup.card_map_of_injective Q.subtype_injective, mul_comm]

omit [Finite G] in
theorem regularCore_le_sylow {Δ : Set G} {Q : Subgroup G} (hQ : IsRegularCore Δ Q)
    (S : Sylow 2 G) (hSN : (S : Subgroup G) ≤ Subgroup.normalizer Δ) : Q ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQn, hQ2, -⟩ := hQ
  have hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) := fun s hs x => by
    constructor
    · intro hx
      exact hQn s (hSN hs) x hx
    · intro hx
      have h := hQn s⁻¹ ((Subgroup.normalizer Δ).inv_mem (hSN hs)) _ hx
      simpa [mul_assoc] using h
  have h2 : IsPGroup 2 ((S : Subgroup G) ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' S.isPGroup' hQ2 hSQ
  have heq := S.is_maximal' h2 le_sup_left
  exact heq ▸ le_sup_right

theorem two_mul_card_le_card_sylow_map {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {U : Subgroup G} (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U) :
    2 * Nat.card U ≤
      Nat.card ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) := by
  classical
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  have huT : hC.d ∈ TG := d_mem_sylow_map hC h3 T
  have hsub : (U : Set G) ∪ (fun v => hC.d * v) '' (U : Set G) ⊆ (TG : Set G) := by
    rintro x (hx | ⟨v, hv, rfl⟩)
    · exact hU.le_sylow_map hx
    · exact TG.mul_mem huT (hU.le_sylow_map hv)
  have hdisj : Disjoint (U : Set G) ((fun v => hC.d * v) '' (U : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨v, hv, rfl⟩
    apply hU.d_not_mem h3
    have : hC.d = hC.d * v * v⁻¹ := by group
    rw [this]
    exact U.mul_mem hx (U.inv_mem hv)
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h)] at hcard
  rw [← Nat.card_coe_set_eq (U : Set G), ← Nat.card_coe_set_eq (TG : Set G)] at hcard
  change Nat.card U + Nat.card U ≤ Nat.card TG at hcard
  omega

theorem exists_central_mem_omega {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {U : Subgroup G} (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((fun v => hC.d * v) '' (U : Set G))) :
    ∃ z ∈ U, z ≠ 1 ∧ ∀ s ∈ (S : Subgroup G), s * z = z * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.isElementaryAbelian
  have hNU := (hU.affine h3).1
  set P : Set G := {x | x ∈ U ∧ x ≠ 1} with hP
  have hSP : ∀ s ∈ (S : Subgroup G), ∀ x ∈ P, s * x * s⁻¹ ∈ P := by
    rintro s hs x ⟨hxU, hx1⟩
    refine ⟨(hNU (hSN hs) x).mp hxU, fun h => hx1 ?_⟩
    have h' : s * x = s := by
      calc s * x = s * x * s⁻¹ * s := by group
        _ = s := by rw [h, one_mul]
    exact mul_eq_left.mp h'
  obtain ⟨e, he, hcard⟩ := hU.exists_card
  have hPcard : Nat.card P = 2 ^ e - 1 := by
    have hPeq : P = (U : Set G) \ {1} := by
      ext x
      simp [hP]
    rw [Nat.card_coe_set_eq, hPeq, Set.ncard_diff_singleton_of_mem (show (1 : G) ∈ (U : Set G)
      from U.one_mem), ← Nat.card_coe_set_eq]
    change Nat.card U - 1 = _
    rw [hcard]
  have hPodd : ¬ 2 ∣ Nat.card P := by
    rw [hPcard]
    intro h
    have h2e : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  let act : MulAction (S : Subgroup G) P :=
    { smul := fun s x => ⟨s * x * s⁻¹, hSP s s.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : (S : Subgroup G)) : G) * x * ((1 : (S : Subgroup G)) : G)⁻¹ = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : (S : Subgroup G)) : G) * x * ((s * t : (S : Subgroup G)) : G)⁻¹ =
          (s : G) * ((t : G) * x * (t : G)⁻¹) * (s : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  obtain ⟨⟨z, hzU, hz1⟩, hzfix⟩ :=
    (S.isPGroup').nonempty_fixed_point_of_prime_not_dvd_card P hPodd
  refine ⟨z, hzU, hz1, fun s hs => ?_⟩
  have h := congrArg Subtype.val (hzfix ⟨s, hs⟩)
  change s * z * s⁻¹ = z at h
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [h]

omit [Finite G] in
theorem mem_commutator_of_mem_omega {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {U : Subgroup G} (hU : DeltaSetup hC T S U) {z : G} (hz : z ∈ U) :
    z ∈ commutator G := by
  have huz : hC.d * z ∈ D := by
    have : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hz, rfl⟩
    exact this.2
  have h := hC.setup.mul_mem_commutator hC.hd huz
  rwa [← mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, one_mul] at h

omit [Finite G] in
theorem wcl_map_le {K : Subgroup G} (z : K) :
    (CFSG.LargeExtraspecial.S11.wcl z).map K.subtype ≤ CFSG.LargeExtraspecial.S11.wcl (z : G) := by
  rw [CFSG.LargeExtraspecial.S11.wcl, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, ⟨m, rfl, hy⟩, rfl⟩
  refine Subgroup.subset_closure ⟨m, by simp, ?_⟩
  simpa using congrArg Subtype.val hy

end CFSG.OddTranspositions.PartThree.Nine
