module

public import CFSG.Quasithin.Vol2.Ch12Sec2Prop27
public import CFSG.Quasithin.Vol2.Ch12Sec2H3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def tr3M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 0, 0, 1]

@[expose] def tr3 : GL (Fin 3) (ZMod 2) := ⟨tr3M, tr3M, by decide, by decide⟩

theorem tr3_mulVec : tr3M.mulVec (Pi.single 0 1) ≠ Pi.single 0 1 := by
  decide

theorem card_multiplicative_fin_three : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd]
  simp

theorem card_GL3 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field]
  decide

theorem stmt12_2_27_three (hM12 : CFSG.GH74.M12.S_Asc03_Theorem1) {G : Type} [Group G]
    [Finite G] {T L V : Subgroup G} (hH : Hyp1223 G T L V) (hE : NoEscape12_2_13 L V)
    (hB : IsLnBlock L 3) (hV : Nat.card V = 2 ^ 3)
    (hML : Subgroup.normalizer (L : Set G) = L) (hVO : V = pCoreOf 2 L)
    (hX : ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L) :
    LieModel G .PSL 4 2 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  obtain ⟨X, hXL, hXV, hXVL⟩ := hX
  obtain ⟨hS, α, hαs, hαker, β, hβs, -, hβeq⟩ := hB
  obtain ⟨-, -, ⟨hUQ, hU2⟩, -, -⟩ := hS
  have hLV := le_normalizer_of_hyp1223 hH
  have hQ : blockQ L = V := by rw [blockQ, hVO]
  have hU : blockU L = V := by
    rw [blockU, hQ]
    exact commutator_eq_of_hyp1223 hH
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := by
    have := hUQ
    rw [hU, hQ] at this
    exact this.trans inf_le_right
  have hVL : V ≤ L := by rw [hVO]; exact Subgroup.map_subtype_le _
  have hUL : blockU L ≤ L := hU.le.trans hVL
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := by rw [hU]; exact hLV
  have hmemV : ∀ l : ↥L, l ∈ CFSG.pCore 2 ↥L ↔ (l : G) ∈ V := fun l => by
    rw [hVO]
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  have hαker' : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ V := fun l => by
    rw [← MonoidHom.mem_ker, hαker]
    exact hmemV l
  have hker : α.ker = (blockU L).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, hαker', Subgroup.mem_subgroupOf, hU]
  obtain ⟨s, hs⟩ := exists_section_of_complement α hαs hαker' hXL hXV hXVL hLV
  have hβbij : Function.Bijective β := hβs.bijective_of_nat_card_le (by
    rw [card_multiplicative_fin_three, hU, hV]
    norm_num)
  obtain ⟨z, hz⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hzV : (z : G) ∈ V := by rw [← hU]; exact z.2
  have hz1 : (z : G) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext h
    have h2 := congrArg Multiplicative.toAdd hz
    rw [h1, map_one, toAdd_one, toAdd_ofAdd] at h2
    exact absurd (congrFun h2 0) (by decide)
  have hord : orderOf (z : G) = 2 := orderOf_eq_prime (hU2 _ z.2) hz1
  have hCL : Subgroup.centralizer ({(z : G)} : Set G) ≤ L :=
    (hE (z : G) hzV hz1).trans hML.le
  let e : ↥(Subgroup.centralizer ({(z : G)} : Set G)) ≃* ↥GL4.H3 :=
    ((Subgroup.subgroupOfEquivOfLe hCL).symm.trans
      (MulEquiv.subgroupCongr (centralizer_subgroupOf_eq (z : G) (hUL z.2)))).trans
      (AffN.centralizerEquivGL hLU α hker s hs β hβeq hUL hβbij z hz)
  have hez : e (GH74.M12.Hyp.zElt' (z : G)) = GL4.tH :=
    Subtype.ext (AffN.psiHom_eq_tGL hLU α hker s hs β hβeq hUL z hz)
  have hloc : GH74.M12.Hyp.LocalHyp ↥(Subgroup.centralizer ({(z : G)} : Set G))
      (GH74.M12.Hyp.zElt' (z : G)) :=
    GH74.M12.Hyp.LocalHyp.of_mulEquiv e.symm (e.symm_apply_eq.mpr hez.symm) GL4.localHyp_H3
  obtain ⟨ℓ, hℓ⟩ := hαs ⟨tr3, mem_statedSL_zmod_two tr3⟩
  have hwmem : (ℓ : G) * z * (ℓ : G)⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (hLU ℓ.2) z).mp z.2
  have hβw : Multiplicative.toAdd (β ⟨_, hwmem⟩) = tr3M.mulVec (Pi.single 0 1) := by
    have h := hβeq ℓ z ⟨_, hwmem⟩ rfl
    rw [hℓ, hz, toAdd_ofAdd] at h
    exact h
  have hwz : (ℓ : G) * z * (ℓ : G)⁻¹ ≠ z := by
    intro h
    have h1 : (⟨_, hwmem⟩ : ↥(blockU L)) = z := Subtype.ext h
    rw [h1, hz, toAdd_ofAdd] at hβw
    exact tr3_mulVec hβw.symm
  have hVz : V ≤ Subgroup.centralizer ({(z : G)} : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hVC hv) (z : G) hzV).symm
  have hwV : (ℓ : G) * z * (ℓ : G)⁻¹ ∈ V := by rw [← hU]; exact hwmem
  have hVcore : V.subgroupOf (Subgroup.centralizer ({(z : G)} : Set G)) ≤
      CFSG.pCore 2 ↥(Subgroup.centralizer ({(z : G)} : Set G)) := by
    refine le_sSup ⟨⟨fun n hn g => ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.mp (hLV (hCL g.2)) n).mp hn
      simpa using this
    · exact (IsPGroup.of_card hV).of_equiv (Subgroup.subgroupOfEquivOfLe hVz).symm
  have hwc : ∃ g : G, g * z * g⁻¹ ≠ z ∧
      ∃ q ∈ CFSG.pCore 2 ↥(Subgroup.centralizer ({(z : G)} : Set G)),
        (q : G) = g * z * g⁻¹ :=
    ⟨ℓ, hwz, ⟨_, hVz hwV⟩, hVcore (Subgroup.mem_subgroupOf.mpr hwV), rfl⟩
  have hasc := GH74.M12.Hyp.asc03Hyp_of_local (z : G) hord hloc hwc
  have hsimple := hH.simple
  rcases hM12 G (z : G) hasc with ⟨W, hWn, -, hW8, ⟨eW⟩⟩ | ⟨hA, -⟩ | ⟨-, hq8⟩
  ·
    exfalso
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · rw [h] at hW8
      simp at hW8
    · have h1 : Nat.card (G ⧸ W) = 1 := by
        show W.index = 1
        rw [h, Subgroup.index_top]
      have h2 := Nat.card_congr eW.toEquiv
      rw [h1, card_GL3] at h2
      omega
  · rcases hA with hA8 | hA9
    · exact Or.inl ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
        G).mpr hA8)
    · exact Or.inr hA9
  ·
    exfalso
    obtain ⟨K, hK, hKn⟩ := GL4.exists_q8_not_normal
    exact hKn (GH74.M12.Hyp.q8_normal_of_mulEquiv e hq8 K hK)

theorem stmt12_2_27_of (hAsc : Asc94_M24He_L52TypeK) (hM12 : CFSG.GH74.M12.S_Asc03_Theorem1)
    (h1226 : Stmt12_2_6) : Stmt12_2_27 := by
  intro G _ _ T L V hH hE n hn hB hV hML hVO hX
  refine ⟨fun h4 => ?_, fun h3 => ?_⟩
  · subst h4
    exact stmt12_2_27_four hAsc h1226 hH hE hB hV hML hVO hX
  · subst h3
    exact stmt12_2_27_three hM12 hH hE hB hV hML hVO hX

end CFSG.Quasithin.H13
