module

public import CFSG.Quasithin.Vol2.Ch11SecANat2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem conjV_conj (V : Subgroup G) {t x : G} (ht : t ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    conjV V t ht * conjV V x hx * (conjV V t ht)⁻¹ =
      conjV V (t * x * t⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hx)
        (Subgroup.inv_mem _ ht)) := by
  rw [← conjV_inv, ← conjV_mul, ← conjV_mul]

theorem mem_stabW_of_map_eq {W : Type*} [Group W] {U : Subgroup W} {τ : MulAut W}
    (hτ : U.map τ.toMonoidHom = U) : τ ∈ stabW U := by
  intro u
  constructor
  · intro hu
    rw [← hτ]
    exact ⟨u, hu, rfl⟩
  · intro hu
    rw [← hτ, mem_map_mulAut] at hu
    simpa using hu

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isSylowTwoOf_inf_L (h : Hyp11 G T L I n) : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
  B6.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)
    le_sup_left (sup_le Subgroup.le_normalizer h.normal)

theorem isSylowTwoOf_P (h : Hyp11 G T L I n) :
    QuasithinUnique.IsSylowTwoOf (autOn (T ⊓ L) (fsuV T I)) (autOn L (fsuV T I)) :=
  isSylowTwoOf_autOn (L_le_normalizer_fsuV h) (isSylowTwoOf_inf_L h)

theorem hasUniqueFlag (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    HasUniqueFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (2 ^ n) := by
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨-, -, -, -, -, hG2⟩
  · exact hF.flagSL3 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h)
  · exact hF.flagSp4 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h)
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    exact hF.flagG2 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h)

omit [Finite G] in
theorem inf_centralizer_subgroupOf (V L : Subgroup G) :
    (V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf V =
      (Subgroup.centralizer (L : Set G)).subgroupOf V :=
  Subgroup.inf_subgroupOf_left _ _

theorem isFlagW_of_isVi (h : Hyp11 G T L I n) {i : ℕ} {U : Subgroup G}
    (hU : IsVi T L I n i U) :
    IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (2 ^ n) i
      (U.subgroupOf (fsuV T I)) := by
  have hL := L_le_normalizer_fsuV h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact IsVi.cV_le hU ⟨z.2, hz⟩
  · have := (isEndStable_iff hL _ U).mp (IsVi.isEndStable hU)
    rwa [inf_centralizer_subgroupOf] at this
  · rw [← inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf (IsVi.le_fsuV hU),
      IsVi.relIndex_eq hU, pow_mul]
  · intro g hg
    obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
    exact (conjV_mem_stabW_iff (IsVi.le_fsuV hU) hxV).mpr (IsVi.le_normalizer hU hx.1)

omit [Finite G] in
theorem mem_normalizer_centralizer {L : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) :
    t ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg l hl
    have hl' : t⁻¹ * l * t ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) l).mp hl
      simpa using this
    have := hg _ hl'
    calc l * (t * g * t⁻¹) = t * ((t⁻¹ * l * t) * g) * t⁻¹ := by group
      _ = t * (g * (t⁻¹ * l * t)) * t⁻¹ := by rw [this]
      _ = t * g * t⁻¹ * l := by group
  · intro hg l hl
    have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht l).mp hl
    have := hg _ hl'
    have e : t * (l * g) * t⁻¹ = t * (g * l) * t⁻¹ := by
      calc t * (l * g) * t⁻¹ = (t * l * t⁻¹) * (t * g * t⁻¹) := by group
        _ = (t * g * t⁻¹) * (t * l * t⁻¹) := this
        _ = t * (g * l) * t⁻¹ := by group
    simpa using e

theorem isVi_of_isFlagW (h : Hyp11 G T L I n) {i : ℕ} {U : Subgroup ↥(fsuV T I)}
    (hU : IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (2 ^ n) i U)
    (huniq : ∀ U', IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (2 ^ n) i U' → U' = U) :
    IsVi T L I n i (U.map (fsuV T I).subtype) := by
  have hL := L_le_normalizer_fsuV h
  have hTV := T_le_normalizer_fsuV T I
  have hsub : (U.map (fsuV T I).subtype).subgroupOf (fsuV T I) = U :=
    Subgroup.comap_map_eq_self_of_injective (fsuV T I).subtype_injective U
  have hle : U.map (fsuV T I).subtype ≤ fsuV T I := Subgroup.map_subtype_le U
  have hTnorm : T ≤ Subgroup.normalizer ((U.map (fsuV T I).subtype : Subgroup G) : Set G) := by
    intro t ht
    have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal ht
    have hτZ : conjV (fsuV T I) t (hTV ht) ∈
        stabW ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) := by
      intro z
      simp only [Subgroup.mem_subgroupOf, conjV_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer htL) z)
    have hτH : ∀ g ∈ autOn L (fsuV T I), conjV (fsuV T I) t (hTV ht) * g *
        (conjV (fsuV T I) t (hTV ht))⁻¹ ∈ autOn L (fsuV T I) := by
      intro g hg
      obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
      rw [conjV_conj]
      exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp htL x).mp hx) _
    have hτP : ∀ g ∈ autOn (T ⊓ L) (fsuV T I), (conjV (fsuV T I) t (hTV ht))⁻¹ * g *
        conjV (fsuV T I) t (hTV ht) ∈ autOn (T ⊓ L) (fsuV T I) := by
      intro g hg
      obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
      have e : (conjV (fsuV T I) t (hTV ht))⁻¹ * conjV (fsuV T I) x hxV *
          conjV (fsuV T I) t (hTV ht) =
          conjV (fsuV T I) t⁻¹ (Subgroup.inv_mem _ (hTV ht)) * conjV (fsuV T I) x hxV *
            (conjV (fsuV T I) t⁻¹ (Subgroup.inv_mem _ (hTV ht)))⁻¹ := by
        rw [conjV_inv, inv_inv]
      rw [e, conjV_conj]
      refine conjV_mem_autOn (Subgroup.mem_inf.mpr ⟨?_, ?_⟩) _
      · exact T.mul_mem (T.mul_mem (T.inv_mem ht) (Subgroup.mem_inf.mp hx).1)
          ((inv_inv t).symm ▸ ht)
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) x).mp
          (Subgroup.mem_inf.mp hx).2
        simpa using this
    have hmap := huniq _ (isFlagW_map hU hτZ hτH hτP)
    have hst : conjV (fsuV T I) t (hTV ht) ∈
        stabW ((U.map (fsuV T I).subtype).subgroupOf (fsuV T I)) := by
      rw [hsub]
      exact mem_stabW_of_map_eq hmap
    exact (conjV_mem_stabW_iff hle (hTV ht)).mp hst
  obtain ⟨hZU, hE, hidx, -⟩ := hU
  refine ⟨⟨?_, hle, ?_, ?_, T, isSylowTwoOf_M h, hTnorm⟩, hTnorm⟩
  · rintro c ⟨hcV, hcL⟩
    exact ⟨⟨c, hcV⟩, hZU hcL, rfl⟩
  · rw [isEndStable_iff hL, hsub, inf_centralizer_subgroupOf]
    exact hE
  · rw [← Subgroup.relIndex_subgroupOf hle, hsub, inf_centralizer_subgroupOf, hidx, ← pow_mul]

theorem eq_map_of_isVi (h : Hyp11 G T L I n) {i : ℕ} {U : Subgroup G} (hU : IsVi T L I n i U)
    {Uk : Subgroup ↥(fsuV T I)}
    (huniq : ∀ U', IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (2 ^ n) i U' → U' = Uk) :
    U = Uk.map (fsuV T I).subtype := by
  rw [← huniq _ (isFlagW_of_isVi h hU), Subgroup.map_subgroupOf_eq_of_le (IsVi.le_fsuV hU)]

end CFSG.Quasithin.Vol2.Ch11.SecA
