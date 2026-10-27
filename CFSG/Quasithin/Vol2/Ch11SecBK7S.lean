module

public import CFSG.Quasithin.Vol2.Ch11SecBK7R
public import CFSG.Quasithin.Vol2.Ch11SecBK7N

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace K7

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem exists_coord_sl3 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSL3 L V n) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSL 3 K) →* ↥(autOn L V)) (f : ↥V → (Fin 3 → K)),
        IsCoord (linModelNat (StatedSL 3 K)) (autOn L V)
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f := by
  obtain ⟨hcomm, hnat⟩ := hfl.nat
  refine ⟨hcomm, ?_⟩
  have hn := hfl.two_le
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
    exact ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf⟩
  · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
    have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
    exact (SecA.kind_not_SL3_Sp4 (by omega) hk ⟨K, inferInstance, inferInstance, hK,
      ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩).elim
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
    obtain ⟨f, hf⟩ := exists_isCoord (G2Q8.lmG K) hπ
    have hbij : Function.Bijective π := by
      refine ⟨fun a b hab => ?_, hf.onto⟩
      set e := MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm with he
      obtain ⟨a', rfl⟩ := e.surjective a
      obtain ⟨b', rfl⟩ := e.surjective b
      exact congrArg e ((G2Q8.rhoG_bijective hf hc0 hc1).1
        (show G2Q8.rhoG hc0 hc1 π a' = G2Q8.rhoG hc0 hc1 π b' from hab))
    exact (SecA.kind_not_SL3_G2 KGNat.factG2DerivedOrder_holds hn hk
      ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩).elim

theorem rootPoint_sl3 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSL3 L V n) {E : Subgroup G}
    (hEX : E ≤ X ⊓ Subgroup.normalizer (V : Set G)) (hEab : CFSG.Open.IsElemAbelian 2 E)
    (hmV : E3.mQuot V (V ⊓ Subgroup.centralizer (E : Set G)) = n)
    (hmE : E3.mQuot E (E ⊓ Subgroup.centralizer (V : Set G)) = n)
    (hcard : Nat.card ↥⁅V, E⁆ ≤ 2 ^ n * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G))) :
    V ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅V, E⁆ ∧
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) ⁅V, E⁆ ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, E⁆ = 2 ^ n := by
  obtain ⟨_, K, _, _, _, hK, π, f, hf⟩ := exists_coord_sl3 hfl hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut ↥V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hZfix := fix_of_autOn (L := L) (V := V)
  have hcomm := commV_autOn_eq_top hfl.le_normalizer hfl.commutator_eq
  have hsq : ∀ u : ↥V, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hfl.elem.2 u u.2)
  have hEV : ∀ {e : G}, e ∈ E → e ∈ Subgroup.normalizer (V : Set G) := fun he => (hEX he).2
  have hEL : ∀ {e : G}, e ∈ E → e ∈ Subgroup.normalizer (L : Set G) := fun he =>
    hfl.normalizer_le (hEX he)
  obtain ⟨c, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hfl.two_le hK
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf V = ⊥ :=
    eq_bot_of_sl3 hc0 hc1 hf hZfix hcomm hsq
  have hCL : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : (⟨z, hz.1⟩ : ↥V) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := hz.2
    rw [hZ] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  have hfinj : ∀ a b : ↥V, f a = f b → a = b := fun a b h => mul_inv_eq_one.mp (by
    have h1 := (hf.eq_iff a b).mp h
    rw [hZ] at h1
    exact Subgroup.mem_bot.mp h1)
  set CE := (V ⊓ Subgroup.centralizer (E : Set G)).subgroupOf V with hCE
  have hidx : CE.index = Nat.card K := by
    obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 ↥V from
      fun w => ⟨1, by rw [pow_one]; exact hsq w⟩)
    have hdvd : CE.index ∣ 2 ^ N := by
      rw [← hN]
      exact CE.index_dvd_card
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hm' : padicValNat 2 CE.index = n := by
      rw [hCE]
      exact hmV
    rw [hk, padicValNat.prime_pow] at hm'
    rw [hk, hm', hK]
  have hZidx : ((Subgroup.centralizer (L : Set G)).subgroupOf V).index = Nat.card K ^ 3 := by
    have htop : hf.img ⊤ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨w, rfl⟩ := hf.surj x
      exact hf.mem_img.mpr ⟨w, Subgroup.mem_top w, rfl⟩
    have h1 := hf.card_img (U := ⊤)
    rw [Subgroup.relIndex_top_right, htop, AddSubgroup.card_top, Nat.card_fun] at h1
    rw [← h1]
    simp
  have hcardCE : Nat.card K ^ 2 ≤ Nat.card (hf.img CE) := by
    rw [hf.card_img]
    have h1 := Subgroup.relIndex_mul_index
      (inf_le_right : (Subgroup.centralizer (L : Set G)).subgroupOf V ⊓ CE ≤ CE)
    rw [Subgroup.inf_relIndex_right, hidx] at h1
    have h3 : ((Subgroup.centralizer (L : Set G)).subgroupOf V).index ≤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V ⊓ CE).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le inf_le_left)
    rw [← h1, hZidx, show Nat.card K ^ 3 = Nat.card K ^ 2 * Nat.card K by ring] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by omega)
  have key : ∀ e (he : e ∈ E), ∃ T : (Fin 3 → K) →ₗ[K] (Fin 3 → K),
      (∀ w, T (f w) = f (SecA.conjV V e (hEV he) w)) ∧ ∀ d ∈ hf.img CE, T d = d := by
    intro e he
    have hinv : (SecA.conjV V e (hEV he))⁻¹ = SecA.conjV V e⁻¹ (Subgroup.inv_mem _ (hEV he)) :=
      (SecA.conjV_inv V (hEV he)).symm
    have he0 : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := fun h =>
      (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h 0)
    have hxZ := fun z hz => G2Q8.conjV_mem_centralizer (hEL he) (hEV he) (z := z) hz
    obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
      he0 (SecA.conjV V e (hEV he)) hxZ (fun z hz => by
        rw [hinv]
        exact G2Q8.conjV_mem_centralizer (Subgroup.inv_mem _ (hEL he))
          (Subgroup.inv_mem _ (hEV he)) hz) (fun h hh => by
        have := G2Q8.conjV_mul_conjV_inv_mem (Subgroup.inv_mem _ (hEL he))
          (Subgroup.inv_mem _ (hEV he)) hh
        rwa [← hinv, inv_inv] at this)
    set T₀ := hf.autMap (SecA.conjV V e (hEV he)) hxZ with hT₀
    have hTf : ∀ w, T₀ (f w) = f (SecA.conjV V e (hEV he) w) := hf.autMap_apply _ hxZ
    have hfixU : ∀ d ∈ hf.img CE, T₀ d = d := by
      rintro _ ⟨u, hu, rfl⟩
      rw [hTf]
      congr 1
      apply Subtype.ext
      have hu' : e * (u : G) = u * e :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hu).2 e he
      rw [SecA.conjV_apply_coe, hu', mul_inv_cancel_right]
    have hfix : Nat.card (hf.img CE) ≤ Nat.card (fixAdd T₀) :=
      Nat.card_le_card_of_injective (fun d => (⟨d.1, hfixU d.1 d.2⟩ : fixAdd T₀))
        fun a b h => Subtype.ext (by have := congrArg Subtype.val h; simpa using this)
    have hM : Nat.card (Fin 3 → K) = Nat.card K ^ 3 := by
      rw [Nat.card_fun]
      simp
    have hσid : ∀ c, σ c = c := semilinear_eq_id_of_card_fix hσ (by
      calc Nat.card (Fin 3 → K) = Nat.card K ^ 3 := hM
        _ < Nat.card K ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
        _ = (Nat.card K ^ 2) ^ 2 := by ring
        _ ≤ Nat.card (fixAdd T₀) ^ 2 := Nat.pow_le_pow_left (hcardCE.trans hfix) 2)
    let TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
      { toFun := T₀
        map_add' := map_add T₀
        map_smul' := fun c v => by rw [hσ, hσid]; rfl }
    exact ⟨TL, hTf, hfixU⟩
  choose Tm hTmf hTmfix using key
  have hEp : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hEab.2 e e.2)⟩
  have hcardE : Nat.card (autOn E V) = Nat.card K := by
    rw [card_autOn_eq_two_pow hEp (fun e he => hEV he) hmE, hK]
  obtain ⟨e₁, he₁, x₀, hx₀⟩ : ∃ e₁, ∃ he₁ : e₁ ∈ E, ∃ x₀, Tm e₁ he₁ x₀ ≠ x₀ := by
    by_contra hno
    push Not at hno
    have htriv : ∀ e (he : e ∈ E), SecA.conjV V e (hEV he) = 1 := fun e he =>
      MulEquiv.ext fun w => hfinj _ _ (by rw [← hTmf e he w, hno e he, MulAut.one_apply])
    have h1 : autOn E V ≤ ⊥ := by
      intro x hx
      obtain ⟨e, he, heV, rfl⟩ := SecA.mem_autOn_iff.mp hx
      exact Subgroup.mem_bot.mpr (htriv e he)
    have h2 : Nat.card (autOn E V) = 1 := by
      rw [le_bot_iff.mp h1, Subgroup.card_bot]
    rw [hcardE] at h2
    omega
  obtain ⟨v, hv0, hrange⟩ := exists_span_eq_range_sub (Tm e₁ he₁) ⟨x₀, hx₀⟩ (by
    refine hcardCE.trans (Nat.card_le_card_of_injective
      (fun d => (⟨d.1, ?_⟩ : LinearMap.ker (Tm e₁ he₁ - LinearMap.id))) ?_)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hTmfix e₁ he₁ d.1 d.2,
        sub_self]
    · intro a b h
      exact Subtype.ext (by have := congrArg Subtype.val h; simpa using this))
  set A := hf.pre (K ∙ v).toAddSubgroup with hA
  have hVE : ⁅V, E⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro x hx e he
    rw [commutatorElement_def, show x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) by group]
    exact V.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hEV he) _).mp (V.inv_mem hx))
  have hAle : A ≤ (⁅V, E⁆).subgroupOf V := by
    intro a ha
    have ha' : f a ∈ LinearMap.range (Tm e₁ he₁ - LinearMap.id) := by
      rw [hrange]
      exact ha
    obtain ⟨x, hx⟩ := ha'
    obtain ⟨w, rfl⟩ := hf.surj x
    have e1 : SecA.conjV V e₁ (hEV he₁) w * w⁻¹ = a := hfinj _ _ (by
      rw [hf.map_mul_inv, ← hTmf, ← hx, LinearMap.sub_apply, LinearMap.id_apply])
    rw [← e1]
    exact conjV_comm_mem he₁ (hEV he₁) w
  have hcardS : Nat.card (K ∙ v).toAddSubgroup = Nat.card K :=
    (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton K _ v hv0).toEquiv).symm
  have hcardA : Nat.card A = Nat.card K := by
    have h1 := hf.card_img (U := A)
    have h2 : ((Subgroup.centralizer (L : Set G)).subgroupOf V).relIndex A = Nat.card A := by
      rw [hZ, Subgroup.relIndex_bot_left]
    rw [h2, hA, hf.img_pre, hcardS] at h1
    rw [hA]
    exact h1.symm
  have hcardVE : Nat.card ((⁅V, E⁆).subgroupOf V) ≤ Nat.card A := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv, hcardA, hK]
    have := hcard
    rwa [hCL, Subgroup.card_bot, mul_one] at this
  have heq : (⁅V, E⁆).subgroupOf V = A := (Subgroup.eq_of_le_of_card_ge hAle hcardVE).symm
  refine ⟨by rw [hCL]; exact bot_le, ?_, ?_⟩
  · rw [SecA.isEndStable_iff hfl.le_normalizer, SecA.inf_centralizer_subgroupOf, heq, hA,
      hf.endStableW_iff hsq (fun T hT => commutant_statedSL (by norm_num) T hT) (hf.le_pre _),
      hf.img_pre]
    exact fun c' x hx => (K ∙ v).smul_mem c' hx
  · rw [← Subgroup.relIndex_subgroupOf hVE, SecA.inf_centralizer_subgroupOf, heq, hA,
      ← hf.card_img, hf.img_pre, hcardS, hK]

end K7

theorem factRootPoint_holds : FactRootPoint := by
  intro G _ _ L V X T V₁ V₂ n hfl E hEX hE hmV hmE hcard
  rcases hfl.kind with hk | hk
  · exact K7.rootPoint_sl3 hfl hk hEX hE hmV hmE hcard
  · exact K7.rootPoint_sp4 hfl hk hEX hE hmV hmE

end CFSG.Quasithin.Vol2.Ch11.SecB
