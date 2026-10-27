module

public import CFSG.Quasithin.Vol2.Ch11SecBK7M
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecBK7C
public import CFSG.Quasithin.Vol2.Ch11SecBK7E
public import CFSG.Quasithin.Vol2.Ch11SecBK7I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped IsMulCommutative commutatorElement

namespace K7

variable {G : Type} [Group G] {V : Subgroup G} [IsMulCommutative ↥V] {K : Type} [Field K]
  {H : Subgroup (MulAut ↥V)} {Z : Subgroup ↥V} {π : ↥(StatedSp 2 K) →* ↥H}
  {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}

theorem acomm_eq_pre (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (hZ : Z ≤ acomm π y) :
    acomm π y = hf.pre (K ∙ y).toAddSubgroup := by
  ext w
  change w ∈ acomm π y ↔ f w ∈ K ∙ y
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hw
    obtain ⟨d, hd⟩ := exists_smul_of_mem_acomm hf hw
    exact ⟨d, hd.symm⟩
  · rintro ⟨d, hd⟩
    obtain ⟨a, ha, hfa⟩ := exists_mem_acomm hf hy d
    have hz : w * a⁻¹ ∈ Z := (hf.eq_iff w a).mp (by rw [← hd, hfa])
    have := (acomm π y).mul_mem (hZ hz) ha
    rwa [inv_mul_cancel_right] at this

theorem card_span_singleton {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) :
    Nat.card (K ∙ y).toAddSubgroup = Nat.card K :=
  (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton K _ y hy).toEquiv).symm

omit [IsMulCommutative ↥V] in
theorem commutator_eq_inv {e : G} (he : e ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ⁅(v : G), e⁆ = (((SecA.conjV V e he v * v⁻¹)⁻¹ : ↥V) : G) := by
  rw [commutatorElement_def, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    SecA.conjV_apply_coe]
  group

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem rootPoint_sp4 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSp4 L V n) {E : Subgroup G}
    (hEX : E ≤ X ⊓ Subgroup.normalizer (V : Set G)) (hEab : CFSG.Open.IsElemAbelian 2 E)
    (hmV : E3.mQuot V (V ⊓ Subgroup.centralizer (E : Set G)) = n)
    (hmE : E3.mQuot E (E ⊓ Subgroup.centralizer (V : Set G)) = n) :
    V ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅V, E⁆ ∧
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) ⁅V, E⁆ ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, E⁆ = 2 ^ n := by
  obtain ⟨_, K, _, _, _, hK, π, f, hf, -, -, -, -⟩ := exists_coord_flag24 hfl hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut ↥V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hZfix := fix_of_autOn (L := L) (V := V)
  have hcomm := commV_autOn_eq_top hfl.le_normalizer hfl.commutator_eq
  have hsq : ∀ u : ↥V, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hfl.elem.2 u u.2)
  have hEV : ∀ {e : G}, e ∈ E → e ∈ Subgroup.normalizer (V : Set G) := fun he => (hEX he).2
  have hEL : ∀ {e : G}, e ∈ E → e ∈ Subgroup.normalizer (L : Set G) := fun he =>
    hfl.normalizer_le (hEX he)
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
  have hZidx : ((Subgroup.centralizer (L : Set G)).subgroupOf V).index = Nat.card K ^ 4 := by
    have htop : hf.img ⊤ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨w, rfl⟩ := hf.surj x
      exact hf.mem_img.mpr ⟨w, Subgroup.mem_top w, rfl⟩
    have h1 := hf.card_img (U := ⊤)
    rw [Subgroup.relIndex_top_right, htop, AddSubgroup.card_top, Nat.card_fun] at h1
    rw [← h1]
    simp
  have hcardCE : Nat.card K ^ 3 ≤ Nat.card (hf.img CE) := by
    rw [hf.card_img]
    have h1 := Subgroup.relIndex_mul_index
      (inf_le_right : (Subgroup.centralizer (L : Set G)).subgroupOf V ⊓ CE ≤ CE)
    rw [Subgroup.inf_relIndex_right, hidx] at h1
    have h3 : ((Subgroup.centralizer (L : Set G)).subgroupOf V).index ≤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V ⊓ CE).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le inf_le_left)
    rw [← h1, hZidx, show Nat.card K ^ 4 = Nat.card K ^ 3 * Nat.card K by ring] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by omega)
  have hxH : ∀ e (he : e ∈ E), ∀ h ∈ autOn L V,
      SecA.conjV V e (hEV he) * h * (SecA.conjV V e (hEV he))⁻¹ ∈ autOn L V :=
    fun e he h hh => G2Q8.conjV_mul_conjV_inv_mem (hEL he) (hEV he) hh
  have key : ∀ e (he : e ∈ E), ∃ Lm : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K),
      (∀ w, Lm (f w) = f (SecA.conjV V e (hEV he) w)) ∧
      (∀ u v, Matrix.toBilin' (spJ K) (Lm u) (Lm v) = Matrix.toBilin' (spJ K) u v) ∧
      ∀ d ∈ hf.img CE, Lm d = d := by
    intro e he
    have hinv : (SecA.conjV V e (hEV he))⁻¹ = SecA.conjV V e⁻¹ (Subgroup.inv_mem _ (hEV he)) :=
      (SecA.conjV_inv V (hEV he)).symm
    have hee : e * e = 1 := by
      have := hEab.2 e he
      rwa [sq] at this
    refine exists_isometry_of_fix hf (fun z hz => G2Q8.conjV_mem_centralizer (hEL he) (hEV he) hz)
      (fun z hz => by
        rw [hinv]
        exact G2Q8.conjV_mem_centralizer (Subgroup.inv_mem _ (hEL he))
          (Subgroup.inv_mem _ (hEV he)) hz) (hxH e he) (fun h hh => ?_) ?_ (fun u hu => ?_)
      hcardCE
    · have := G2Q8.conjV_mul_conjV_inv_mem (Subgroup.inv_mem _ (hEL he))
        (Subgroup.inv_mem _ (hEV he)) hh
      rwa [← hinv, inv_inv] at this
    · rw [← SecA.conjV_mul]
      ext v
      rw [SecA.conjV_apply_coe, hee, one_mul, inv_one, mul_one, MulAut.one_apply]
    · apply Subtype.ext
      have hu' : e * (u : G) = u * e :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hu).2 e he
      rw [SecA.conjV_apply_coe, hu', mul_inv_cancel_right]
  choose Lm hLmf hLmB hLmfix using key
  have hEp : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hEab.2 e e.2)⟩
  have hcardE : Nat.card (autOn E V) = Nat.card K := by
    rw [card_autOn_eq_two_pow hEp (fun e he => hEV he) hmE, hK]
  have hex : ∃ e₁, ∃ he₁ : e₁ ∈ E, ∃ x₀, Lm e₁ he₁ x₀ ≠ x₀ := by
    by_contra hno
    push Not at hno
    have htriv : ∀ e (he : e ∈ E), SecA.conjV V e (hEV he) = 1 := fun e he =>
      eq_one_of_modZ hf hZfix hcomm (hxH e he) fun w => by rw [← hLmf e he w, hno e he]
    have h1 : autOn E V ≤ ⊥ := by
      intro x hx
      obtain ⟨e, he, heV, rfl⟩ := SecA.mem_autOn_iff.mp hx
      exact Subgroup.mem_bot.mpr (htriv e he)
    have h2 : Nat.card (autOn E V) = 1 := by
      rw [le_bot_iff.mp h1, Subgroup.card_bot]
    rw [hcardE] at h2
    omega
  obtain ⟨e₁, he₁, x₀, hx₀⟩ := hex
  obtain ⟨y, hy, hc⟩ := exists_common_centre (ι := ↥E) (fun e => Lm e e.2)
    (fun e => hLmB e e.2) (D₀ := (hf.img CE : Set (Fin 2 ⊕ Fin 2 → K)))
    (fun e d hd => hLmfix e e.2 d hd) hcardCE (i₀ := ⟨e₁, he₁⟩) hx₀
  have hact : ∀ e (he : e ∈ E), ∃ c : K,
      SecA.conjV V e (hEV he) = ((π (trv y c) : ↥(autOn L V)) : MulAut ↥V) := by
    intro e he
    obtain ⟨c, hc'⟩ := hc ⟨e, he⟩
    have hc'' : ∀ x, Lm e he x = mat 2 K (trv y c) *ᵥ x := hc'
    exact ⟨c, eq_pi_of_modZ hf hZfix hcomm (hxH e he) fun w => by rw [← hLmf e he w, hc'']⟩
  choose c hcE using hact
  have hψ : ∀ x : ↥(autOn E V), ∃ c' : K,
      ((π (trv y c') : ↥(autOn L V)) : MulAut ↥V) = x := by
    intro x
    obtain ⟨e, he, heV, hx⟩ := SecA.mem_autOn_iff.mp x.2
    exact ⟨c e he, by rw [← hcE e he, hx]⟩
  choose ψ hψ using hψ
  have hψinj : Function.Injective ψ := fun x x' h =>
    Subtype.ext (by rw [← hψ x, ← hψ x', h])
  have hψbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hψinj, hcardE⟩
  have hall : ∀ c' : K, ∃ e, ∃ he : e ∈ E,
      SecA.conjV V e (hEV he) = ((π (trv y c') : ↥(autOn L V)) : MulAut ↥V) := by
    intro c'
    obtain ⟨x, hx⟩ := hψbij.2 c'
    obtain ⟨e, he, heV, hxe⟩ := SecA.mem_autOn_iff.mp x.2
    exact ⟨e, he, by rw [← hx, hψ x]; exact hxe.symm⟩
  obtain ⟨l, hl0, hl1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hfl.two_le hK
  have hZle := le_acomm hf hZfix hcomm hsq hl0 hl1 hy
  have hle1 : acomm π y ≤ (⁅V, E⁆).subgroupOf V := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨c', u, rfl⟩
    obtain ⟨e, he, he'⟩ := hall c'
    rw [← he']
    exact conjV_comm_mem he (hEV he) u
  have hle2 : ⁅V, E⁆ ≤ (acomm π y).map V.subtype := by
    rw [Subgroup.commutator_le]
    intro v hv e he
    refine ⟨(SecA.conjV V e (hEV he) ⟨v, hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹)⁻¹, ?_, ?_⟩
    · refine (acomm π y).inv_mem ?_
      rw [hcE e he]
      exact gen_mem_acomm π y _ _
    · exact (commutator_eq_inv (hEV he) ⟨v, hv⟩).symm
  have hVE : ⁅V, E⁆ ≤ V := hle2.trans (Subgroup.map_subtype_le _)
  have heq : (⁅V, E⁆).subgroupOf V = acomm π y := by
    refine le_antisymm (fun u hu => ?_) hle1
    obtain ⟨a, ha, hau⟩ := hle2 (Subgroup.mem_subgroupOf.mp hu)
    have : a = u := Subtype.ext hau
    rwa [← this]
  have hpre := acomm_eq_pre hf hy hZle
  refine ⟨le_commutator_of_le_acomm hZle hle1, ?_, ?_⟩
  · rw [SecA.isEndStable_iff hfl.le_normalizer, SecA.inf_centralizer_subgroupOf, heq, hpre,
      hf.endStableW_iff hsq (fun T hT => commutant_statedSp T hT) (hf.le_pre _), hf.img_pre]
    exact fun c' x hx => (K ∙ y).smul_mem c' hx
  · rw [← Subgroup.relIndex_subgroupOf hVE, SecA.inf_centralizer_subgroupOf, heq, hpre,
      ← hf.card_img, hf.img_pre, card_span_singleton hy, hK]

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
