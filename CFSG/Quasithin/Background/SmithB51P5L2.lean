module

public import CFSG.Quasithin.Background.SmithB51P5Fix
public import CFSG.Quasithin.Background.SmithB51P5SL2
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B5Irr
public import CFSG.Quasithin.Background.FFC5Ext
public import CFSG.Quasithin.Background.SmithB51P5Basic

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open Matrix CFSG.Quasithin.JonesParshall

namespace B5

namespace P5

section L2

variable {V : Type} [CommGroup V]

theorem det_statedSL {n : ℕ} {K : Type} [Field K] (γ : ↥(StatedSL n K)) :
    ((γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h := (specialLinearGroupEquivStatedSL n K).apply_symm_apply γ
  rw [← h, specialLinearGroupEquivStatedSL_coe]
  exact ((specialLinearGroupEquivStatedSL n K).symm γ).2

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hc : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hc])

theorem mul_self_eq_one_of_fixed_class {L : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (hnat : BinaryNaturalSL L U Z 2 n) {l : MulAut V} (hl : l ∈ L) {s : V} (hs : s ∈ U)
    (hsZ : s ∉ Z) (hfix : l s * s⁻¹ ∈ Z) : l * l = 1 := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hnat
  have := charP_two_of_card hc
  obtain ⟨f, -, hfk, hfe⟩ := G64.exists_natMap hπ
  obtain ⟨γ, hγ⟩ := hπ.1 ⟨l, hl⟩
  have hγl : ((π γ : ↥L) : MulAut V) = l := by rw [hγ]
  have hu : ((π γ : ↥L) : MulAut V) s ∈ U := by
    rw [hγl]
    exact hπ.2.2.2.1 ⟨l, hl⟩ s hs
  have h1 := hfe γ ⟨s, hs⟩ hu
  have h2 : f ⟨((π γ : ↥L) : MulAut V) s, hu⟩ = f ⟨s, hs⟩ := by
    have h3 : f (⟨((π γ : ↥L) : MulAut V) s, hu⟩ * ⟨s, hs⟩⁻¹) = 1 := by
      refine (hfk _).2 ?_
      show ((π γ : ↥L) : MulAut V) s * s⁻¹ ∈ Z
      rw [hγl]
      exact hfix
    rwa [map_mul, map_inv, mul_inv_eq_one] at h3
  have h4 : f ⟨s, hs⟩ ≠ 1 := fun h0 => hsZ ((hfk _).1 h0)
  have hMx : ((((show ↥(StatedSL 2 K) from γ)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      Multiplicative.toAdd (f ⟨s, hs⟩) = Multiplicative.toAdd (f ⟨s, hs⟩) := by
    have := congrArg Multiplicative.toAdd (h1.symm.trans h2)
    exact this
  have hx : Multiplicative.toAdd (f ⟨s, hs⟩) ≠ 0 := fun h0 =>
    h4 (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
  have hMM := mul_self_eq_one_of_mulVec_eq (det_statedSL (show ↥(StatedSL 2 K) from γ)) hx hMx
  have hγγ : γ * γ = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hMM
  calc l * l = ((π (γ * γ) : ↥L) : MulAut V) := by rw [map_mul, Subgroup.coe_mul, hγl]
    _ = 1 := by rw [hγγ, map_one]; rfl

variable [Finite V] {G L : Subgroup (MulAut V)}

theorem eq_of_binaryNaturalSL_two (h : B51Hyp G L) (h1 : B51Part1 G L) {n : ℕ}
    (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n) : G = L := by
  rcases h1.2 with hi | hii | ⟨k, hiii⟩ | hiv
  · obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
    rcases hi.2.2 T hT with hGL | ⟨hGT, hmod⟩
    · exact hGL
    · exfalso
      obtain ⟨g, hgL, hg3, ⟨s, hsU, hsZ, hfix⟩, ⟨s₁, -, hmove⟩⟩ :=
        exists_order_three_of_case1i h hT hGT hmod
      have hgg := mul_self_eq_one_of_fixed_class hnat hgL hsU hsZ hfix
      have hg1 : g = 1 := by
        calc g = g ^ 3 * (g * g)⁻¹ := by group
          _ = 1 := by rw [hg3, hgg]; group
      apply hmove
      rw [hg1, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
  · exact hii.1
  · exact hiii.1
  · exact hiv.1

theorem sup_fixV_eq_top_of_l2 (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (h1 : B51Part1 G L)
    {n : ℕ} (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n) :
    commV L ⊔ fixV G = ⊤ := by
  have hGL := eq_of_binaryNaturalSL_two h h1 hnat
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hnat
  have := charP_two_of_card hc
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.exists_natMap hπ
  set ψ := specialLinearGroupEquivStatedSL 2 K with hψ
  set π' : SL2 K →* ↥L := π.comp ψ.toMonoidHom with hπ'
  have hπ'surj : Function.Surjective π' := hπ.1.comp ψ.surjective
  have hLU : ∀ g ∈ L, ∀ u ∈ commV L, g u ∈ commV L := fun g hg u hu => hπ.2.2.2.1 ⟨g, hg⟩ u hu
  have hfe' : ∀ (g : SL2 K) (u : ↥(commV L)) (hu : ((π' g : ↥L) : MulAut V) u ∈ commV L),
      Multiplicative.toAdd (f ⟨_, hu⟩) = g • Multiplicative.toAdd (f u) := by
    intro g u hu
    have := congrArg Multiplicative.toAdd (hfe (ψ g) u hu)
    refine this.trans ?_
    show ((ψ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ _ =
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ _
    rw [specialLinearGroupEquivStatedSL_coe]
  have hπ'inj : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfix : ∀ x : Fin 2 → K, g • x = x := by
      intro x
      obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd x)
      have hmem : ((π' g : ↥L) : MulAut V) (u : V) ∈ commV L := hLU _ (π' g).2 _ u.2
      have h1 := hfe' g u hmem
      have h2 : (⟨((π' g : ↥L) : MulAut V) (u : V), hmem⟩ : ↥(commV L)) = u := by
        apply Subtype.ext
        show ((π' g : ↥L) : MulAut V) (u : V) = u
        rw [hg]
        rfl
      rw [h2, hu, toAdd_ofAdd] at h1
      exact h1.symm
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h1 := congrFun (hfix (Pi.single j 1)) i
    change ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single j 1) i = _ at h1
    rw [mulVec_single_one] at h1
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1
  have hUcard : Nat.card ↥(commV L) = Nat.card K ^ 2 * Nat.card ↥(fixV L ⊓ commV L) := by
    rw [G64.RealizesVia.card_eq hπ, G64.card_natMod]
  obtain ⟨A, hA⟩ := exists_offender h
  have hAL : A ≤ L := hGL ▸ hA.1
  set Ab : Subgroup (SL2 K) := (A.subgroupOf L).comap π' with hAb
  have hAbcard : Nat.card Ab = Nat.card A := by
    rw [← Subgroup.card_map_of_injective (K := Ab) hπ'inj,
      Subgroup.map_comap_eq_self_of_surjective hπ'surj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
  have hAb2 : IsPGroup 2 Ab := by
    refine IsPGroup.comap_of_injective ?_ π' hπ'inj
    exact hA.2.2.1.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm
  obtain ⟨e, he0, he⟩ := exists_fixed_ne_zero hc hAb2
  have hAbstab : Ab ≤ MulAction.stabilizer (SL2 K) e := fun g hg => he g hg
  have hAbK : Nat.card Ab ≤ Nat.card K :=
    (Subgroup.card_le_of_le hAbstab).trans (card_stabilizer_le he0)
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
  have ha1' : a ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
  obtain ⟨g, hg⟩ := hπ'surj ⟨a, hAL haA⟩
  have hga : ((π' g : ↥L) : MulAut V) = a := by rw [hg]
  have hg1 : g ≠ 1 := fun h0 => ha1' (by rw [← hga, h0, map_one]; rfl)
  have hCA : Nat.card ↥(commV L ⊓ fixV A) ≤ Nat.card ↥(fixV L ⊓ commV L) * Nat.card K := by
    set Hs : Subgroup ↥(commV L) := (fixV A).subgroupOf (commV L) with hHs
    have hHscard : Nat.card Hs = Nat.card ↥(commV L ⊓ fixV A) :=
      Nat.card_congr
        { toFun := fun x => ⟨((x : ↥(commV L)) : V), (x : ↥(commV L)).2, x.2⟩
          invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    set Fx : Subgroup (Multiplicative (Fin 2 → K)) :=
      { carrier := {x | g • Multiplicative.toAdd x = Multiplicative.toAdd x}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_ofPred_eq, toAdd_mul, smul_add] at hx hy ⊢
          rw [hx, hy]
        one_mem' := by simp
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_ofPred_eq, toAdd_inv, smul_neg] at hx ⊢
          rw [hx] } with hFx
    have hFxK : Nat.card Fx ≤ Nat.card K := by
      refine le_trans (le_of_eq ?_) (card_fixed_le hg1)
      exact Nat.card_congr
        { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (Fin 2 → K)), x.2⟩
          invFun := fun w => ⟨Multiplicative.ofAdd w.1, w.2⟩
          left_inv := fun x => rfl
          right_inv := fun w => rfl }
    have hmap : Hs.map f ≤ Fx := by
      rintro _ ⟨u, hu, rfl⟩
      have hmem : ((π' g : ↥L) : MulAut V) (u : V) ∈ commV L := hLU _ (π' g).2 _ u.2
      have h1 := hfe' g u hmem
      have h2 : (⟨((π' g : ↥L) : MulAut V) (u : V), hmem⟩ : ↥(commV L)) = u := by
        apply Subtype.ext
        show ((π' g : ↥L) : MulAut V) (u : V) = u
        rw [hga]
        exact hu a haA
      rw [h2] at h1
      exact h1.symm
    have hker : Nat.card ↥(Hs ⊓ f.ker) ≤ Nat.card ↥(fixV L ⊓ commV L) := by
      refine le_trans (Subgroup.card_le_of_le inf_le_right) (le_of_eq ?_)
      exact Nat.card_congr
        { toFun := fun u => ⟨((u : ↥(commV L)) : V), (hfk u).1 u.2⟩
          invFun := fun z => ⟨⟨z, z.2.2⟩, (hfk ⟨z, z.2.2⟩).2 z.2⟩
          left_inv := fun u => rfl
          right_inv := fun z => rfl }
    have h3 := B1More.card_map_mul_card_inf_ker Hs f
    rw [← hHscard, ← h3, mul_comm]
    exact Nat.mul_le_mul hker ((Subgroup.card_le_of_le hmap).trans hFxK)
  obtain ⟨hsupA, hcardA⟩ := sup_fixV_eq_top_of_card_le hA (U := commV L) (by
    rw [hUcard, ← hAbcard]
    calc Nat.card Ab * Nat.card ↥(commV L ⊓ fixV A)
        ≤ Nat.card K * (Nat.card ↥(fixV L ⊓ commV L) * Nat.card K) := Nat.mul_le_mul hAbK hCA
      _ = Nat.card K ^ 2 * Nat.card ↥(fixV L ⊓ commV L) := by ring)
  have hAK : Nat.card K ≤ Nat.card Ab := by
    by_contra hlt
    push Not at hlt
    have hZpos : 0 < Nat.card ↥(fixV L ⊓ commV L) := Nat.card_pos
    have hKpos : 0 < Nat.card K := Nat.card_pos
    rw [hUcard, ← hAbcard] at hcardA
    have : Nat.card Ab * Nat.card ↥(commV L ⊓ fixV A) <
        Nat.card K * (Nat.card ↥(fixV L ⊓ commV L) * Nat.card K) :=
      Nat.mul_lt_mul_of_lt_of_le hlt hCA (Nat.mul_pos hZpos hKpos)
    rw [hcardA] at this
    nlinarith
  have hAbeq : Ab = MulAction.stabilizer (SL2 K) e :=
    Subgroup.eq_of_le_of_card_ge hAbstab ((card_stabilizer_le he0).trans hAK)
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hc, this] at h1
    simp at h1
  have hodd : Odd (A.subgroupOf L).index := by
    rw [← Subgroup.index_comap_of_surjective (A.subgroupOf L) hπ'surj]
    show Odd Ab.index
    rw [hAbeq]
    exact odd_index_stabilizer hc hn1 he0
  have hsupL := FFC.sup_fixV_eq_top_of_odd hLU
    (fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩) hV hodd hsupA
  rw [hGL]
  exact hsupL

end L2

end P5

end B5

end CFSG.Quasithin
