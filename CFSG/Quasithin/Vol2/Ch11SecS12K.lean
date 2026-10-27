module

public import CFSG.Quasithin.Vol2.Ch11SecS12D
public import CFSG.Quasithin.Vol2.Ch11SecS12I
public import CFSG.Quasithin.Vol2.Ch11SecQ9bL2pC
public import CFSG.Quasithin.Vol2.Ch11SecS12G

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecD
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open CFSG.Quasithin.OperatorJH
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G]

theorem lt_of_isNatEig {K C₁ C₂ : Subgroup G} {x : G} {m : ℕ} [NeZero m] {F : Type} [Field F]
    {α₀ : ↥K →* ↥(StatedSL m F)} {a : F} (h : IsNatEigSection K x α₀ C₁ C₂ a)
    (hC : C₁ ≤ C₂) : C₁ < C₂ := by
  refine lt_of_le_of_ne hC fun heq => ?_
  obtain ⟨β, hβs, hβk, -, -⟩ := h
  obtain ⟨c, hc⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have h1 : (c : G) ∈ C₁ := heq ▸ c.2
  have h2 := (hβk c).mpr h1
  rw [hc] at h2
  have := congrArg (fun w : Multiplicative (Fin m → F) => Multiplicative.toAdd w 0) h2
  simp at this

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem almostSpecialL3Hyp_star (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (hG2 : SecA.FactG2DerivedOrder) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hSL3 : KindSL3 L (fsuV T I) n)
    (hU : ¬ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 (L ⊔ T)) :
    AlmostSpecialL3Hyp n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨hcomm, -, -, -, hc⟩ := h1102 G T L I n h
  have hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases (h1103 G T L I n h).2.2.1 with ⟨h1, -⟩ | ⟨hk, -⟩
    · exact h1
    · rcases hk with hk | hk
      · exact (SecA.kind_not_SL3_Sp4 (by omega) hSL3 hk).elim
      · exact (SecA.kind_not_SL3_G2 hG2 hn hSL3 hk).elim
  have hnat : IsNaturalSL3Module n L (pCoreOf 2 (L ⊔ T)) (fsuV T I) V₁ := by
    rcases hc with ⟨K, _, _, hK, he, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩
    · exact isNaturalSL3Module_of_cV h1102 h hV₁ hCV hK he π hπ
    · exact (SecA.kind_not_SL3_Sp4 (by omega) hSL3 ⟨K, inferInstance, inferInstance, hK, he⟩).elim
    · exact (SecA.kind_not_SL3_G2 hG2 hn hSL3 ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  obtain ⟨D⟩ := hnat.nonempty_data
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hLV := SecA.L_le_normalizer_fsuV h
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hlOne : LOf L V₁ ≤ lOne L V₁ := by
    have h1 : oTwoUpper (LOf L V₁) = LOf L V₁ :=
      C2Nine.oTwoUpper_eq_of_perfect (perfectCore_perfect _)
    rw [← h1]
    exact oTwoUpper_mono (perfectCore_le _)
  have hlOneL : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  have h1 : ∀ w : Fin 3 → GaloisField 2 n, D.θ ⟨1, L.one_mem⟩ • w = (1 : GaloisField 2 n) • w :=
    fun w => by
      rw [one_smul]
      have : (⟨1, L.one_mem⟩ : ↥L) = 1 := rfl
      rw [this, map_one, one_smul]
  have hnatV := NatData3'.natEig_V D hV₁V L.one_mem h1
  have hlt : V₁ < fsuV T I := lt_of_isNatEig hnatV hV₁V
  have hVeq : fsuV T I = conjClosure V₁ L := by
    refine le_antisymm ?_ (conjClosure_le fun l hl w hw =>
      (Subgroup.mem_normalizer_iff.mp (hLV hl) w).mp (hV₁V hw))
    obtain ⟨g, hg, k, hk, -, -, hV⟩ := exists_weyl' D hV₁V
    have hconj : ∀ a ∈ L, rconj V₁ a ≤ conjClosure V₁ L := fun a ha w hw => by
      rw [mem_rconj] at hw
      have := mem_conjClosure (L.inv_mem ha) hw
      simpa [mul_assoc] using this
    rw [hV]
    exact sup_le (sup_le (le_conjClosure V₁ L) (hconj g hg)) (hconj k hk)
  have hV₁O : V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))
  have hO2ne : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := fun hb =>
    SecA.IsVi.ne_bot h hV₁ le_rfl (le_bot_iff.mp (hb ▸ hV₁O))
  refine ⟨⟨SecA.isElemAbelian_fsuV h, SecA.IsVi.ne_bot h hV₁ le_rfl, hV₁V,
    (C2Nine.oTwoUpper_eq_of_perfect (perfect_of_hyp11 h)).symm, SecA.fsuV_le_T h, hTN,
    SecA.T_le_normalizer_fsuV T I, h.normal,
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right, le_rfl,
    sup_le (hlOneL.trans inf_le_right) hTN, isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN,
    charTwo_of_inH h.fsu.qtke.2.1 (h.fsu.sylow.1.toSylow h.fsu.sylow.2)
      (H := Subgroup.normalizer (V₁ : Set G))
      (by rw [IsPGroup.toSylow_coe]; exact ⟨hTN, hO2ne⟩), ?_⟩, by omega, hVeq, hnat, hU⟩
  refine ⟨hlt, sup_le ((hlOneL.trans inf_le_left).trans hLV) (SecA.T_le_normalizer_fsuV T I),
    sup_le (hlOneL.trans inf_le_right) hTN, fun W hV₁W hWV hWN => ?_⟩
  exact hnatV.eq_or_eq le_rfl (NatData3'.alpha0_surjective D hn hV₁V)
    (NatData3'.lOf_le.trans hLV) hV₁W hWV (hlOne.trans (le_sup_left.trans hWN))

theorem isSL3_four_of (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hSL3 : KindSL3 L (fsuV T I) 2) :
    IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨_, -, -, ⟨eL⟩, -⟩ := h1102 G T L I 2 h
  obtain ⟨F, _, _, hF, ⟨eS⟩⟩ := hSL3
  exact ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num,
    ⟨eL.trans (eS.trans (statedSLEquiv' 3 F).symm)⟩⟩

theorem pCoreOf_le_pCoreOf_LT (h : Hyp11 G T L I n) : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
  have hE : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (sup_le Subgroup.le_normalizer h.normal).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((Subgroup.map_subtype_le _).trans le_sup_left) hE
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem exists_scalar_of_xOne (hFb : SecA.Facts12b) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) {V₁ V₂ X : Subgroup G} (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X) (hSL3 : KindSL3 L (fsuV T I) 2)
    (D : NatData3 2 L (pCoreOf 2 (L ⊔ T)) (fsuV T I) V₁) {x : G}
    (hx : x ∈ SecA.xOne X (LOf L V₁)) (hxL : x ∈ L) :
    ∃ c : GaloisField 2 2, c ^ 3 = 1 ∧
      ∀ w : Fin 3 → GaloisField 2 2, D.θ ⟨x, hxL⟩ • w = c • w := by
  have hSL := isSL3_four_of h1102 h hSL3
  have hcomm : ∀ A : SL(3, GaloisField 2 2), D.θ ⟨x, hxL⟩ * A = A * D.θ ⟨x, hxL⟩ := by
    intro A
    obtain ⟨l, rfl⟩ := D.surj A
    have h1 := SecA.C11P9B.commutator_mem_of_isSL3 hFb hN h1102 h hV₁ hV₂ hX hSL hx l.2
    have h2 : (⟨x, hxL⟩ * l * ⟨x, hxL⟩⁻¹ * l⁻¹ : ↥L) ∈ D.θ.ker := by
      rw [D.ker_eq, Subgroup.mem_subgroupOf]
      exact pCoreOf_le_pCoreOf_LT h h1
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 := congrArg (· * D.θ l) h2
    simp only [inv_mul_cancel_right, one_mul] at h3
    have h4 := congrArg (· * D.θ ⟨x, hxL⟩) h3
    simpa [mul_assoc] using h4
  have hcen : D.θ ⟨x, hxL⟩ ∈ Subgroup.center SL(3, GaloisField 2 2) :=
    Subgroup.mem_center_iff.mpr fun A => (hcomm A).symm
  obtain ⟨c, hc3, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  refine ⟨c, by simpa using hc3, fun w => ?_⟩
  rw [Matrix.SpecialLinearGroup.smul_def, ← hcA]
  simp [Matrix.scalar_apply]

theorem scalar_ne_one_of_xOne {V₁ X : Subgroup G}
    (D : NatData3 2 L (pCoreOf 2 (L ⊔ T)) (fsuV T I) V₁)
    (hX₁ : Nat.card ↥(SecA.xOne X (LOf L V₁)) = 3) {x : G}
    (hx : x ∈ SecA.xOne X (LOf L V₁)) (hx1 : x ≠ 1) (hxL : x ∈ L) {c : GaloisField 2 2}
    (hxc : ∀ w : Fin 3 → GaloisField 2 2, D.θ ⟨x, hxL⟩ • w = c • w) : c ≠ 1 := by
  rintro rfl
  have hθ : D.θ ⟨x, hxL⟩ = 1 := by
    apply Subtype.ext
    ext i j
    have := smul_single_one (D.θ ⟨x, hxL⟩) j i
    rw [hxc, one_smul] at this
    rw [← this]
    simp [Pi.single_apply, Matrix.one_apply]
  have hO : x ∈ pCoreOf 2 (L ⊔ T) := by
    have h2 : (⟨x, hxL⟩ : ↥L) ∈ D.θ.ker := hθ
    rw [D.ker_eq, Subgroup.mem_subgroupOf] at h2
    exact h2
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨x, hO⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : orderOf x ∣ 3 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(SecA.xOne X (LOf L V₁)))
    rwa [hX₁, Subgroup.orderOf_mk] at this
  have h4 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h5 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)) h3 h4
  exact hx1 (orderOf_eq_one_iff.mp h5)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
