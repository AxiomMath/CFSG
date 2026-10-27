module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanT
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mem_sup_of_odd {A Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ Q)
    (hodd : Odd (orderOf x)) : x ∈ A := by
  have hAn : (A.subgroupOf (A ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQA)
  have hx' : x ∈ (↑(A ⊔ Q) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA] at hx'
  obtain ⟨a, ha, q, hq, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  set π := QuotientGroup.mk' (A.subgroupOf (A ⊔ Q))
  set y : ↥(A ⊔ Q) := ⟨a * q, hx⟩
  have hqa : q⁻¹ * a⁻¹ * q ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hQA hq)) a⁻¹).mp (A.inv_mem ha)
    simpa using this
  have hπ : π y = π ⟨q, Subgroup.mem_sup_right hq⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [y, mul_assoc] using hqa
  have h1 : π y ^ orderOf (a * q) = 1 := by
    rw [← map_pow]
    have : y ^ orderOf (a * q) = 1 := Subtype.ext (by simp [y, pow_orderOf_eq_one])
    rw [this, map_one]
  have h2 : π y ^ (2 ^ k) = 1 := by
    rw [hπ, ← map_pow]
    have : (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(A ⊔ Q)) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hcop : Nat.Coprime (orderOf (a * q)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hcop.gcd_eq_one, pow_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h3
  exact h3

variable {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem autOn_le_normalizer {S X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (S : Set G)) :
    autOn X V ≤ Subgroup.normalizer (autOn S V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hX

omit [Finite G] in
theorem tL_inf (T L : Subgroup G) : TL T L ⊓ L = T ⊓ L := by
  change T ⊓ (L ⊔ pCoreOf 2 (L ⊔ T)) ⊓ L = T ⊓ L
  rw [inf_assoc, inf_eq_right.mpr (le_sup_left : L ≤ L ⊔ pCoreOf 2 (L ⊔ T))]

omit [Finite G] in
theorem mem_normalizer_inf_of_mem {T L : Subgroup G} {x : G} (hxL : x ∈ L)
    (hxT : x ∈ Subgroup.normalizer (TL T L : Set G)) :
    x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  rw [← tL_inf T L]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxT, Subgroup.le_normalizer hxL⟩

theorem cartan_le_normalizer_Vi (hF : SecA.NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {i : ℕ} (hi : i = 1 ∨ i = 2) {U X : Subgroup G} (hU : IsVi T L I n i U)
    (hX : IsCartanX T L X) : X ≤ Subgroup.normalizer (U : Set G) := by
  intro x hx
  have hxL : x ∈ L := (hX.1 hx).1
  have hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G) := L_le_normalizer_fsuV h hxL
  have hUV : U ≤ fsuV T I := IsVi.le_fsuV hU
  have hxTL := mem_normalizer_inf_of_mem hxL (hX.1 hx).2
  have hσZ : conjV (fsuV T I) x hxV ∈
      stabW ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) := by
    rw [← inf_centralizer_subgroupOf, conjV_mem_stabW_iff inf_le_left hxV]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hxV, mem_normalizer_centralizer (Subgroup.le_normalizer hxL)⟩
  have hσH : ∀ g ∈ autOn L (fsuV T I),
      conjV (fsuV T I) x hxV * g * (conjV (fsuV T I) x hxV)⁻¹ ∈ autOn L (fsuV T I) :=
    fun g hg => (Subgroup.mem_normalizer_iff.mp (autOn_le_normalizer
      (Subgroup.le_normalizer : L ≤ _) (conjV_mem_autOn hxL hxV)) g).mp hg
  have hσP : ∀ g ∈ autOn (T ⊓ L) (fsuV T I),
      (conjV (fsuV T I) x hxV)⁻¹ * g * conjV (fsuV T I) x hxV ∈
        autOn (T ⊓ L) (fsuV T I) := by
    have hmem := autOn_le_normalizer
      (le_rfl : Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ _)
      (conjV_mem_autOn hxTL hxV)
    intro g hg
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmem) g).mp hg
    simpa using this
  have hflag := isFlagW_of_isVi h hU
  have hflag' := isFlagW_map hflag hσZ hσH hσP
  obtain ⟨U₁, U₂, U₃, -, -, -, -, -, hu₁, hu₂, -⟩ := hasUniqueFlag hF h1102 h
  have heq : (U.subgroupOf (fsuV T I)).map (conjV (fsuV T I) x hxV).toMonoidHom =
      U.subgroupOf (fsuV T I) := by
    rcases hi with rfl | rfl
    · exact (hu₁ _ hflag').trans (hu₁ _ hflag).symm
    · exact (hu₂ _ hflag').trans (hu₂ _ hflag).symm
  exact (conjV_mem_stabW_iff hUV hxV).mp (mem_stabW_of_map_eq heq)

theorem cartan_le_normalizer_lOf (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) {i : ℕ} (hi : i = 1 ∨ i = 2) {U X : Subgroup G}
    (hU : IsVi T L I n i U) (hX : IsCartanX T L X) :
    X ≤ Subgroup.normalizer (LOf L U : Set G) := by
  refine le_trans ?_ (normalizer_le_normalizer_perfectCore _)
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (hX.1 hx).1,
      Subgroup.le_normalizer (cartan_le_normalizer_Vi hF h1102 h hi hU hX hx)⟩

theorem cartan_inf_centralizer (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {X : Subgroup G}
    (hX : IsCartanX T L X) : X ⊓ Subgroup.centralizer (fsuV T I : Set G) = ⊥ := by
  have hle : X ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 L ⊓ X := by
    rw [← centralizer_eq_pCoreOf h1102 h]
    exact le_inf (inf_le_inf_right _ fun x hx => (hX.1 hx).1) inf_le_left
  have := inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hX.2.1
  exact eq_bot_iff.mpr (this ▸ hle)

end CFSG.Quasithin.Vol2.Ch11.SecS
