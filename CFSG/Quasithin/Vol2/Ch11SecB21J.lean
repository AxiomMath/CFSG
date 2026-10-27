module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts21
public import CFSG.Quasithin.Vol2.Ch11SecB21Cent

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped IsMulCommutative commutatorElement

section General

variable {G : Type} [Group G]

theorem commutatorElement_mul_central_left {Q : Type*} [Group Q] (a b z : Q)
    (hz : ∀ g : Q, g * z = z * g) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hz b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_right {Q : Type*} [Group Q] (a b z : Q)
    (hz : ∀ g : Q, g * z = z * g) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hz a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_or_central_of_normal [Finite G] {X N : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    N = X ∨ ∀ y ∈ N, ∀ x ∈ X, ⁅y, x⁆ ∈ pCoreOf 2 X := by
  have hNn : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  set Q := ↥X ⧸ CFSG.pCore 2 ↥X
  set Z := Subgroup.center Q
  have hmapZ : (((N.subgroupOf X).map π).map (QuotientGroup.mk' Z)).Normal :=
    ((Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)).map _
      (QuotientGroup.mk'_surjective _))
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hq.2.1 _ hmapZ with h | h
  ·
    right
    intro y hy x hx
    have hyZ : π ⟨y, hNX hy⟩ ∈ Z := by
      have h1 : QuotientGroup.mk' Z (π ⟨y, hNX hy⟩) ∈
          ((N.subgroupOf X).map π).map (QuotientGroup.mk' Z) :=
        ⟨_, ⟨⟨y, hNX hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h2 : π ⁅(⟨y, hNX hy⟩ : ↥X), ⟨x, hx⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hyZ _).symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  ·
    left
    set H := (N.subgroupOf X).map π
    have hHZ : ∀ q : Q, ∃ h ∈ H, ∃ z ∈ Z, h * z = q := by
      intro q
      have hq' : QuotientGroup.mk' Z q ∈ H.map (QuotientGroup.mk' Z) := h ▸ Subgroup.mem_top _
      obtain ⟨h₀, hh₀, he⟩ := hq'
      refine ⟨h₀, hh₀, h₀⁻¹ * q, ?_, by group⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at he
      exact he
    have hHtop : H = ⊤ := by
      refine eq_top_iff.mpr ((Group.isPerfect_def.1 hq.1).symm.le.trans ?_)
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := hHZ a
      obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hHZ b
      have e : ⁅h₁ * z₁, h₂ * z₂⁆ = ⁅h₁, h₂⁆ := by
        rw [commutatorElement_mul_central_left _ _ _ (Subgroup.mem_center_iff.mp hz₁),
          commutatorElement_mul_central_right _ _ _ (Subgroup.mem_center_iff.mp hz₂)]
      rw [e, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
    set N' := N.subgroupOf X
    have hNn' : N'.Normal := hNn
    set φ := QuotientGroup.mk' N'
    have h2 : IsPGroup 2 (↥X ⧸ N') := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N' y
      have hx : π x ∈ H := hHtop ▸ Subgroup.mem_top _
      obtain ⟨m, hm, hme⟩ := hx
      have hp : m⁻¹ * x ∈ CFSG.pCore 2 ↥X := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hme
        exact hme
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥X)) ⟨_, hp⟩
      refine ⟨k, ?_⟩
      have hk' : (m⁻¹ * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hφm : φ m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      calc QuotientGroup.mk' N' x ^ 2 ^ k = (φ m * φ (m⁻¹ * x)) ^ 2 ^ k := by
            rw [← map_mul, mul_inv_cancel_left]
        _ = φ ((m⁻¹ * x) ^ 2 ^ k) := by rw [hφm, one_mul, map_pow]
        _ = 1 := by rw [hk', map_one]
    have hperf : commutator (↥X ⧸ N') = ⊤ := by
      have hXp : commutator ↥X = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hX)
      have hsurj := QuotientGroup.mk'_surjective N'
      calc commutator (↥X ⧸ N') = ⁅(⊤ : Subgroup (↥X ⧸ N')), ⊤⁆ := commutator_def _
        _ = ⁅(⊤ : Subgroup ↥X).map φ, (⊤ : Subgroup ↥X).map φ⁆ := by
            rw [Subgroup.map_top_of_surjective φ hsurj]
        _ = Subgroup.map φ ⁅(⊤ : Subgroup ↥X), ⊤⁆ := (Subgroup.map_commutator _ _ _).symm
        _ = ⊤ := by rw [← commutator_def, hXp, Subgroup.map_top_of_surjective φ hsurj]
    have hsub : Subsingleton (↥X ⧸ N') := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent (↥X ⧸ N') := h2.isNilpotent
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥X ⧸ N')).ne hperf
    refine le_antisymm hNX fun x hx => ?_
    have h1 : QuotientGroup.mk' N' ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1

theorem commutator_mem_centralizer_of_central {L V : Subgroup G} {j : G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hL : ⁅L, L⁆ = L)
    (hjV : j ∈ Subgroup.normalizer (V : Set G)) (hjL : j ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ l ∈ L, ∀ x ∈ L, ⁅⁅j, l⁆, x⁆ ∈ Subgroup.centralizer (V : Set G)) :
    ∀ l ∈ L, ⁅j, l⁆ ∈ Subgroup.centralizer (V : Set G) := by
  have hjl : ∀ l ∈ L, j * l * j⁻¹ ∈ L := fun l hl => (Subgroup.mem_normalizer_iff.mp hjL l).mp hl
  have hmemL : ∀ l ∈ L, ⁅j, l⁆ ∈ L := fun l hl => by
    rw [commutatorElement_def]
    exact L.mul_mem (hjl l hl) (L.inv_mem hl)
  have hmemN : ∀ l ∈ L, ⁅j, l⁆ ∈ Subgroup.normalizer (V : Set G) := fun l hl => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hjV (hLV hl))
      (Subgroup.inv_mem _ hjV)) (Subgroup.inv_mem _ (hLV hl))
  have hcomm : ∀ l ∈ L, ∀ x ∈ L, ∀ w ∈ V,
      ⁅j, l⁆ * (x * w * x⁻¹) * ⁅j, l⁆⁻¹ = x * (⁅j, l⁆ * w * ⁅j, l⁆⁻¹) * x⁻¹ := by
    intro l hl x hx w hw
    set c := ⁅j, l⁆
    have hw' : x * (c * w * c⁻¹) * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hx) _).mp
        ((Subgroup.mem_normalizer_iff.mp (hmemN l hl) w).mp hw)
    have h1 := Subgroup.mem_centralizer_iff.mp (hc l hl x hx) _ hw'
    rw [commutatorElement_def] at h1
    calc c * (x * w * x⁻¹) * c⁻¹
        = (c * x * c⁻¹ * x⁻¹) * (x * (c * w * c⁻¹) * x⁻¹) * (c * x * c⁻¹ * x⁻¹)⁻¹ := by group
      _ = x * (c * w * c⁻¹) * x⁻¹ := by
          rw [← h1, mul_inv_cancel_right]
  let f : ↥L →* MulAut ↥V :=
    { toFun := fun l => conjV V ⁅j, (l : G)⁆ (hmemN l l.2)
      map_one' := by
        ext v
        simp [conjV_apply_coe]
      map_mul' := by
        intro a b
        ext v
        simp only [MulAut.mul_apply, conjV_apply_coe, Subgroup.coe_mul]
        have hv' : (a : G)⁻¹ * v * a ∈ V := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem a.2)) v).mp v.2
        have h2 := hcomm b b.2 a a.2 _ hv'
        have e : ⁅j, (a : G) * b⁆ = ⁅j, (a : G)⁆ * (a * ⁅j, (b : G)⁆ * (a : G)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        calc ⁅j, (a : G)⁆ * (a * ⁅j, (b : G)⁆ * (a : G)⁻¹) * v *
              (⁅j, (a : G)⁆ * (a * ⁅j, (b : G)⁆ * (a : G)⁻¹))⁻¹
            = ⁅j, (a : G)⁆ * (a * (⁅j, (b : G)⁆ * ((a : G)⁻¹ * v * a) * ⁅j, (b : G)⁆⁻¹) *
                (a : G)⁻¹) * ⁅j, (a : G)⁆⁻¹ := by group
          _ = ⁅j, (a : G)⁆ * (⁅j, (b : G)⁆ * (a * ((a : G)⁻¹ * v * a) * (a : G)⁻¹) *
                ⁅j, (b : G)⁆⁻¹) * ⁅j, (a : G)⁆⁻¹ := by rw [← h2]
          _ = ⁅j, (a : G)⁆ * (⁅j, (b : G)⁆ * v * ⁅j, (b : G)⁆⁻¹) * ⁅j, (a : G)⁆⁻¹ := by group }
  have hfc : ∀ a b : ↥L, f a * f b = f b * f a := by
    intro a b
    ext v
    simp only [MulAut.mul_apply]
    show ((conjV V ⁅j, (a : G)⁆ (hmemN a a.2) (conjV V ⁅j, (b : G)⁆ (hmemN b b.2) v) : ↥V) : G) =
      ((conjV V ⁅j, (b : G)⁆ (hmemN b b.2) (conjV V ⁅j, (a : G)⁆ (hmemN a a.2) v) : ↥V) : G)
    simp only [conjV_apply_coe]
    exact hcomm a a.2 _ (hmemL b b.2) v v.2
  have hf1 : ∀ a : ↥L, f a = 1 := by
    have htop : commutator ↥L = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hL)
    have hrange : ⁅f.range, f.range⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, rfl⟩
      exact hfc b a
    intro a
    have ha : a ∈ commutator ↥L := htop ▸ Subgroup.mem_top a
    have hmap : f a ∈ (commutator ↥L).map f := ⟨a, ha, rfl⟩
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange,
      Subgroup.mem_bot] at hmap
    exact hmap
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h3 := congrArg (fun φ : MulAut ↥V => ((φ ⟨w, hw⟩ : ↥V) : G)) (hf1 ⟨l, hl⟩)
  simp only [MulAut.one_apply] at h3
  change ((conjV V ⁅j, l⁆ (hmemN l hl) ⟨w, hw⟩ : ↥V) : G) = w at h3
  rw [conjV_apply_coe] at h3
  calc w * ⁅j, l⁆ = ⁅j, l⁆ * w * ⁅j, l⁆⁻¹ * ⁅j, l⁆ := by rw [h3]
    _ = ⁅j, l⁆ * w := by group

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem natModuleOf_fsuV (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) :
    NatModuleOf L (fsuV T I) n := by
  obtain ⟨hab, -, -, -, hmod⟩ := h1102 G T L I n hyp
  refine ⟨hab, ?_⟩
  rcases hmod with ⟨K, hK, hKf, hKc, -, π, hπ, -⟩ | ⟨K, hK, hKf, hKc, -, π, hπ, -⟩ |
    ⟨K, hK, hKf, hKc, -, hG2⟩
  · exact Or.inl ⟨K, hK, hKf, hKc, π, hπ⟩
  · exact Or.inr (Or.inl ⟨K, hK, hKf, hKc, π, hπ⟩)
  · exact Or.inr (Or.inr hG2)

theorem isPGroup_cL_fsuV (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  rw [centralizer_eq_pCoreOf h1102 hyp]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L

theorem eq_commutator_thompsonJ (hFC : FactCentralizerTwo) (h1102 : Stmt11_0_2)
    (hyp : Hyp11 G T L I n)
    (hJ : ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :
    L = ⁅L, thompsonJ T⁆ := by
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJL : thompsonJ T ≤ Subgroup.normalizer (L : Set G) := hJT.trans hyp.normal
  have hLperf : ⁅L, L⁆ = L := hyp.fsu.faithful.1.2.1.2.1
  have hNL : ⁅L, thompsonJ T⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hJL
  rcases eq_or_central_of_normal hLperf hyp.fsu.quasisimple hNL
      (Subgroup.normalizer_commutator_ge_left L (thompsonJ T)) with h | hcen
  · exact h.symm
  exfalso
  apply hJ
  intro j hj
  refine ⟨hJT hj, ?_⟩
  have hLV := L_le_normalizer_fsuV hyp
  have hjV : j ∈ Subgroup.normalizer (fsuV T I : Set G) := T_le_normalizer_fsuV T I (hJT hj)
  have hO2 := centralizer_eq_pCoreOf h1102 hyp
  have hnat := natModuleOf_fsuV h1102 hyp
  have h2 : ∃ k : ℕ, j ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hyp.fsu.sylow.1 ⟨j, hJT hj⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine hFC G L (fsuV T I) n (isElemAbelian_fsuV hyp) hyp.one_lt hLV
    (commutator_fsuV_eq_self hyp) hnat j hjV (hJL hj) h2 fun l hl => ?_
  have hc : ∀ l ∈ L, ∀ x ∈ L, ⁅⁅j, l⁆, x⁆ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro l hl x hx
    have hy : ⁅j, l⁆ ∈ ⁅L, thompsonJ T⁆ := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hl hj)
    have := hcen _ hy x hx
    rw [← hO2] at this
    exact this.2
  have := commutator_mem_centralizer_of_central hLV hLperf hjV (hJL hj) hc l hl
  rwa [commutatorElement_def] at this

end CFSG.Quasithin.Vol2.Ch11.SecB
