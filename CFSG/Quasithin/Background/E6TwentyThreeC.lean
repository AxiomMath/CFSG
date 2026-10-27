module

public import CFSG.Quasithin.Background.E6TwentyThreeB
public import CFSG.Quasithin.EmptyFaithful.S152He10B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent
public import CFSG.Quasithin.Background.C2PushBlocks

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mul_inv_mem_of_mem_closure {N B : Subgroup G} {S : Set G}
    (hS : S ⊆ Subgroup.normalizer (N : Set G))
    (h : ∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ N) {b : G} (hb : b ∈ B) {z : G}
    (hz : z ∈ Subgroup.closure S) : b * z * b⁻¹ * z⁻¹ ∈ N := by
  have hzN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G) := (Subgroup.closure_le _).2 hS
  induction hz using Subgroup.closure_induction with
  | mem s hs => exact h b hb s hs
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxN := hzN hx
    have e : b * (x * y) * b⁻¹ * (x * y)⁻¹ =
        (b * x * b⁻¹ * x⁻¹) * (x * (b * y * b⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact N.mul_mem ihx ((Subgroup.mem_normalizer_iff.1 hxN _).1 ihy)
  | inv x hx ihx =>
    have hxN := hzN hx
    have e : b * x⁻¹ * b⁻¹ * x⁻¹⁻¹ = x⁻¹ * (b * x * b⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) _).1 (N.inv_mem ihx)

omit [Finite G] in
theorem map_conj_mem_cComp {H X : Subgroup G} (hX : X ∈ cComp H) {q : G} (hq : q ∈ H) :
    X.map (MulAut.conj q).toMonoidHom ∈ cComp H := by
  have h1 := cComp_map_mulEquiv (MulAut.conj q) hX
  have h2 : H.map (MulAut.conj q).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hq)
  rwa [h2] at h1

omit [Finite G] in
theorem map_conj_le_conjClosure {X Q : Subgroup G} {q : G} (hq : q ∈ Q) :
    X.map (MulAut.conj q).toMonoidHom ≤ conjClosure X Q := by
  rintro _ ⟨z, hz, rfl⟩
  exact mem_conjClosure hq hz

omit [Finite G] in
theorem conjClosure_le_of_le {X Q H : Subgroup G} (hXH : X ≤ H) (hQH : Q ≤ H) :
    conjClosure X Q ≤ H :=
  conjClosure_le fun _ hh _ hz => H.mul_mem (H.mul_mem (hQH hh) (hXH hz)) (H.inv_mem (hQH hh))

theorem exists_eq_map_conj_of_mem_cComp (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {H Q X B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hQH : Q ≤ H) (hX : X ∈ cComp H)
    (hB : B ∈ cComp H) (hBY : B ≤ conjClosure X Q) :
    ∃ q ∈ Q, B = X.map (MulAut.conj q).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  have hXH : X ≤ H := le_of_mem_cComp hX
  set S : Set G := {x | ∃ h ∈ Q, ∃ z ∈ X, h * z * h⁻¹ = x} with hSdef
  have hSN : S ⊆ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := by
    rintro _ ⟨h, hh, z, hz, rfl⟩
    exact le_normalizer_pCoreOf 2 H
      (H.mul_mem (H.mul_mem (hQH hh) (hXH hz)) (H.inv_mem (hQH hh)))
  have hc : ∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ pCoreOf 2 H := by
    rintro b hb _ ⟨h, hh, z, hz, rfl⟩
    have hXq := map_conj_mem_cComp hX (hQH hh)
    have h2 := Vol2Native.lemma_1_2_1_two hK h37 hH hB hXq (hall h hh)
    have hmem : ⁅b, h * z * h⁻¹⁆ ∈ ⁅B, X.map (MulAut.conj h).toMonoidHom⁆ :=
      Subgroup.commutator_mem_commutator hb ⟨z, hz, rfl⟩
    have h3 := h2.2 (h2.1 hmem)
    rwa [commutatorElement_def] at h3
  have hBB : ⁅B, B⁆ ≤ pCoreOf 2 H := by
    rw [Subgroup.commutator_le]
    intro b hb b' hb'
    rw [commutatorElement_def]
    exact conj_mul_inv_mem_of_mem_closure hSN hc hb (hBY hb')
  rw [perfect_of_mem_cComp hB] at hBB
  apply not_isSolvable_of_mem_cComp hB
  have h2 : IsPGroup 2 ↥B := (pCoreOf_isPGroup 2 H).to_le hBB
  have : Group.IsNilpotent ↥B := h2.isNilpotent
  infer_instance

theorem charTwo_conjClosure_sup (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {H Q X : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hQ : IsSylowTwoOf Q H) (hO : oddCoreIn H = ⊥) (hX : X ∈ cComp H)
    (hXq : ¬ CFSG.IsQuasisimple ↥X) : CharTwo (conjClosure X Q ⊔ Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := conjClosure X Q with hYdef
  have hQH : Q ≤ H := hQ.1
  have hYH : Y ≤ H := conjClosure_le_of_le (le_of_mem_cComp hX) hQH
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hK h37 h38 hH hQ hX
  have hQY : Q ≤ Subgroup.normalizer (Y : Set G) := hQH.trans hHY
  have hQ2 : IsPGroup 2 Q := hQ.2.1
  have hYn : (Y.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).2 hHY
  have hYsn : IsSubnormal Y H := A3.subnormal_of_normal hYH hYn
  refine DoubleA3.charTwo_of_no_component (fun Z hZ => ?_) ?_
  ·
    have hZc : Z ∈ cComp (Y ⊔ Q) := Vol2Native.mem_cComp_of_isComponentIn hZ
    have hZq := BenderBranch.isQuasisimple_of_isComponentIn hZ
    have hZY : Z ≤ Y := C2Push.le_of_perfect_le_sup hQ2 hQY (perfect_of_mem_cComp hZc) hZ.1
    have hZH : Z ∈ cComp H := cComp_mem_of_subnormal hYsn (cComp_mem_of_le hZc hZY le_sup_left)
    obtain ⟨q, -, rfl⟩ := exists_eq_map_conj_of_mem_cComp hK h37 hH hQH hX hZH hZY
    exact hXq (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective X _ (MulAut.conj q).injective).symm hZq)
  ·
    set O := oddCoreIn (Y ⊔ Q) with hOdef
    have hOK : O ≤ Y ⊔ Q := CFSG.QuasithinUnique.oddCoreIn_le _
    have hOodd : Odd (Nat.card O) := CFSG.QuasithinUnique.odd_card_oddCoreIn _
    have hOY : O ≤ Y := by
      intro x hx
      obtain ⟨k, hk⟩ := Setup.Campbell.exists_pow_mem_of_mem_sup_pGroup hQ2 hQY (hOK hx)
      have hodd : Odd (orderOf x) := by
        have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : O)
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hOodd h1
      exact B6.mem_of_pow_mem_of_coprime hk
        (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd))
    have hON : Y ≤ Subgroup.normalizer (O : Set G) :=
      le_sup_left.trans (CFSG.QuasithinUnique.le_normalizer_oddCoreIn _)
    have hO1 : O ≤ oddCoreIn Y := DoubleA3.le_oddCoreIn_of_odd hOY hON hOodd
    have hOY1 : oddCoreIn Y ≤ oddCoreIn H := oddCoreIn_le_of_subnormal'' hYH hYn.isSubnormal
    rw [hO] at hOY1
    exact le_bot_iff.1 (hO1.trans hOY1)

omit [Finite G] in
theorem mem_normalizer_of_forall_commute {H : Type*} [Group H] {A : Subgroup H} {g : H}
    (h : ∀ a ∈ A, Commute g a) : g ∈ Subgroup.normalizer (A : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [(h a ha).eq, mul_inv_cancel_right]
    exact ha
  · intro ha
    have h1 := (h _ ha).eq
    have h3 : g * (g * a * g⁻¹) = g * a := by rw [h1]; group
    rw [mul_left_cancel h3] at ha
    exact ha

omit [Finite G] in
theorem threeCentral_map_equiv {Z W : Type*} [Group Z] [Group W] {S : Subgroup Z} (e : Z ≃* W)
    (h : ∀ D : Subgroup Z, D ≤ S → (D.subgroupOf S).Normal → IsPGroup 3 D →
      ∀ d ∈ D, ∀ l ∈ S, Commute d l) :
    ∀ D : Subgroup W, D ≤ S.map e.toMonoidHom → (D.subgroupOf (S.map e.toMonoidHom)).Normal →
      IsPGroup 3 D → ∀ d ∈ D, ∀ l ∈ S.map e.toMonoidHom, Commute d l := by
  intro D hD hDn hD3 d hd l hl
  set D₁ : Subgroup Z := D.map e.symm.toMonoidHom with hD₁
  have hmemD₁ : ∀ z, z ∈ D₁ ↔ e z ∈ D := by
    intro z
    rw [hD₁, Subgroup.mem_map_equiv]
    simp
  have hmemK : ∀ z, z ∈ S ↔ e z ∈ S.map e.toMonoidHom := by
    intro z
    rw [Subgroup.mem_map_equiv]
    simp
  have hD₁K : D₁ ≤ S := fun z hz => (hmemK z).mpr (hD ((hmemD₁ z).mp hz))
  have hKN : S.map e.toMonoidHom ≤ Subgroup.normalizer (D : Set W) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hD).mp hDn
  have hD₁n : (D₁.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD₁K]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.mp (hKN ((hmemK k).mp hk)) (e z)
    rw [hmemD₁, hmemD₁]
    simpa using h1
  have hD₁3 : IsPGroup 3 D₁ :=
    hD3.map e.symm.toMonoidHom |>.of_equiv
      (MulEquiv.subgroupCongr (by rfl : D₁ = D.map e.symm.toMonoidHom)).symm
  have hd' : e.symm d ∈ D₁ := by
    rw [hD₁, Subgroup.mem_map_equiv]
    simpa using hd
  have hl' : e.symm l ∈ S := (hmemK (e.symm l)).mpr (by simpa using hl)
  have := h D₁ hD₁K hD₁n hD₁3 (e.symm d) hd' (e.symm l) hl'
  have h2 := congrArg e this.eq
  simp only [map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

omit [Finite G] in
theorem commute_of_perfect_normal' {Z : Type*} [Group Z] {L P B : Subgroup Z} (hL : ⁅L, L⁆ = L)
    [hLn : L.Normal] [hPn : P.Normal] (hP3 : IsPGroup 3 P) (hB : B ≤ P)
    (hA : ∀ D : Subgroup Z, D ≤ L → (D.subgroupOf L).Normal → IsPGroup 3 D →
      ∀ d ∈ D, ∀ l ∈ L, Commute d l) :
    ∀ x ∈ L, ∀ y ∈ B, Commute x y := by
  set D : Subgroup Z := L ⊓ P with hD
  have hDK : D ≤ L := inf_le_left
  have hDn : (D.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDK]
    intro k _
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer_of_normal (H := L) (K := ⊤) (Subgroup.mem_top k),
        Subgroup.le_normalizer_of_normal (H := P) (K := ⊤) (Subgroup.mem_top k)⟩
  have hD3 : IsPGroup 3 D := hP3.to_le inf_le_right
  have hDc := hA D hDK hDn hD3
  have hKB : ⁅L, B⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨?_, ?_⟩
    · have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact L.mul_mem hx (hLn.conj_mem _ (L.inv_mem hx) y)
    · have : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact P.mul_mem (hPn.conj_mem y (hB hy) x) (P.inv_mem (hB hy))
  have hBK : ⁅B, L⁆ ≤ D := by
    rw [Subgroup.commutator_comm]
    exact hKB
  have hDK' : ∀ E : Subgroup Z, E ≤ D → ⁅E, L⁆ = ⊥ := by
    intro E hE
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hDc a (hE ha) b hb)
  have h1 : ⁅⁅L, B⁆, L⁆ = ⊥ := hDK' _ hKB
  have h2 : ⁅⁅B, L⁆, L⁆ = ⊥ := hDK' _ hBK
  have h3 : ⁅⁅L, L⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hL] at h3
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅L, B⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h3, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem threeCentral_conjClosure (hQT : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) {K Q X : Subgroup G} (hKne : pCoreOf 2 K ≠ ⊥)
    (hQK : Q ≤ K) (hX : X ∈ cComp K) :
    ∀ D : Subgroup (OTwoQuot K), D ≤ imageOTwoQuot K (conjClosure X Q) →
      (D.subgroupOf (imageOTwoQuot K (conjClosure X Q))).Normal → IsPGroup 3 D →
      ∀ d ∈ D, ∀ l ∈ imageOTwoQuot K (conjClosure X Q), Commute d l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥K →* OTwoQuot K := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) with hπ
  set Y := conjClosure X Q with hYdef
  have hYK : Y ≤ K := conjClosure_le_of_le (le_of_mem_cComp hX) hQK
  have hXcK : ∀ q ∈ Q, X.map (MulAut.conj q).toMonoidHom ∈ cComp K := fun q hq =>
    map_conj_mem_cComp hX (hQK hq)
  have hAY : ∀ q ∈ Q, imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom) ≤
      imageOTwoQuot K Y := fun q hq =>
    Subgroup.map_mono fun _ hx => map_conj_le_conjClosure hq hx
  have hTCA : ∀ q ∈ Q, ∀ D : Subgroup (OTwoQuot K),
      D ≤ imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom) →
      (D.subgroupOf (imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom))).Normal →
      IsPGroup 3 D → ∀ d ∈ D, ∀ l ∈ imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom),
        Commute d l := by
    intro q hq
    have hA36 := lemma_1_2_1_four_strong hQT hs hnab h36 hKne (hXcK q hq)
    let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* OTwoQuot K :=
      QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)
    have hmap : imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom) =
        (modO2Image K (X.map (MulAut.conj q).toMonoidHom)).map e.toMonoidHom := by
      unfold imageOTwoQuot modO2Image
      rw [Subgroup.map_map]
      congr 1
    rw [hmap]
    exact threeCentral_map_equiv e fun _ hDL hDn hD3 =>
      He10.commute_of_normal_threeGroup hA36 hDL hDn hD3
  have hAperf : ∀ q ∈ Q, ⁅imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom),
      imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom)⁆ =
      imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom) := by
    intro q hq
    obtain ⟨e⟩ :=
      C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (subnormal_of_mem_cComp (hXcK q hq))
    have : Group.IsPerfect ↥(X.map (MulAut.conj q).toMonoidHom) :=
      Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp (hXcK q hq))
    have : Group.IsPerfect (↥(X.map (MulAut.conj q).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(X.map (MulAut.conj q).toMonoidHom)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have : Group.IsPerfect ↥(imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom)) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Subgroup.isPerfect_iff.mp this
  have hcomm : ∀ q ∈ Q, ∀ q' ∈ Q,
      X.map (MulAut.conj q).toMonoidHom ≠ X.map (MulAut.conj q').toMonoidHom →
      ∀ a ∈ imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom),
      ∀ a' ∈ imageOTwoQuot K (X.map (MulAut.conj q').toMonoidHom), Commute a a' := by
    intro q hq q' hq' hne a ha a' ha'
    obtain ⟨x, hx, hxq, rfl⟩ := mem_imageOTwoQuot_iff.mp ha
    obtain ⟨x', hx', hxq', rfl⟩ := mem_imageOTwoQuot_iff.mp ha'
    have h2 := Vol2Native.lemma_1_2_1_two hK h37 hKne (hXcK q hq) (hXcK q' hq') hne
    have hc : ⁅x, x'⁆ ∈ pCoreOf 2 K := h2.2 (h2.1 (Subgroup.commutator_mem_commutator hxq hxq'))
    have hc' : ⁅(⟨x, hx⟩ : ↥K), ⟨x', hx'⟩⁆ ∈ CFSG.Open.pCore 2 ↥K := by
      rw [← Subgroup.mem_map_iff_mem K.subtype_injective, map_commutatorElement]
      exact hc
    have h3 : ⁅π ⟨x, hx⟩, π ⟨x', hx'⟩⁆ = 1 := by
      rw [← map_commutatorElement, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc'
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  have hgen : ∀ h ∈ Q, ∀ z ∈ X, ∀ hx : h * z * h⁻¹ ∈ K,
      π ⟨h * z * h⁻¹, hx⟩ ∈ imageOTwoQuot K (X.map (MulAut.conj h).toMonoidHom) :=
    fun h _ z hz hx => mem_imageOTwoQuot_iff.mpr ⟨_, hx, ⟨z, hz, rfl⟩, rfl⟩
  have hYle : ∀ P : Subgroup (OTwoQuot K), (∀ h ∈ Q, ∀ z ∈ X, ∀ hx : h * z * h⁻¹ ∈ K,
      π ⟨h * z * h⁻¹, hx⟩ ∈ P) → imageOTwoQuot K Y ≤ P := by
    intro P hP
    have hYW : Y ≤ (P.comap π).map K.subtype := by
      refine conjClosure_le fun h hh z hz => ?_
      have hx : h * z * h⁻¹ ∈ K := hYK (mem_conjClosure hh hz)
      exact ⟨⟨h * z * h⁻¹, hx⟩, hP h hh z hz hx, rfl⟩
    rintro _ ⟨⟨y, hyK⟩, hyY, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hYW (show y ∈ Y from hyY)
    have hwy' : w = ⟨y, hyK⟩ := Subtype.ext hwy
    rw [← hwy']
    exact hw
  have hYNA : ∀ q ∈ Q, imageOTwoQuot K Y ≤
      Subgroup.normalizer (imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom) :
        Set (OTwoQuot K)) := by
    intro q hq
    refine hYle _ fun h hh z hz hx => ?_
    have hmem := hgen h hh z hz hx
    by_cases he : X.map (MulAut.conj h).toMonoidHom = X.map (MulAut.conj q).toMonoidHom
    · rw [he] at hmem
      exact Subgroup.le_normalizer hmem
    · exact mem_normalizer_of_forall_commute fun a ha => hcomm h hh q hq he _ hmem a ha
  intro D hDY hDn hD3 d hd l hl
  have hYND : imageOTwoQuot K Y ≤ Subgroup.normalizer (D : Set (OTwoQuot K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).1 hDn
  have hDA : ∀ q ∈ Q, ∀ x ∈ D, ∀ a ∈ imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom),
      Commute x a := by
    intro q hq
    set A := imageOTwoQuot K (X.map (MulAut.conj q).toMonoidHom) with hAdef
    have hAY' : A ≤ imageOTwoQuot K Y := hAY q hq
    have hNA := hYNA q hq
    have hc1 : ⁅D, A⁆ ≤ D ⊓ A := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h1 : a * x⁻¹ * a⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.1 (hYND (hAY' ha)) _).1 (D.inv_mem hx)
        have h2 := D.mul_mem hx h1
        simpa [mul_assoc] using h2
      · rw [commutatorElement_def]
        have h1 : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hNA (hDY hx)) _).1 ha
        exact A.mul_mem h1 (A.inv_mem ha)
    have hEn : ((D ⊓ A).subgroupOf A).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro a ha
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hYND (hAY' ha), Subgroup.le_normalizer ha⟩
    have hE := hTCA q hq (D ⊓ A) inf_le_right hEn (hD3.to_le inf_le_left)
    have h1 : ⁅⁅D, A⁆, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hE c (hc1 hc) a ha).eq.symm
    have h2 : ⁅⁅A, D⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm A D]; exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    rw [hAperf q hq] at h3
    intro x hx a ha
    have h4 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3 ha
    exact Subgroup.mem_centralizer_iff.1 h4 x hx
  have hYC : imageOTwoQuot K Y ≤ Subgroup.centralizer (D : Set (OTwoQuot K)) := by
    refine hYle _ fun h hh z hz hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx'
    exact (hDA h hh x hx' _ (hgen h hh z hz hx)).eq
  exact Subgroup.mem_centralizer_iff.1 (hYC hl) d hd

theorem le_of_all_A3_of_threeCentral {K M₁ L : Subgroup G} (hLK : L ≤ K)
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) (hLperf : ⁅L, L⁆ = L) (hM₁K : M₁ ≤ K)
    (hOK : pCoreOf 2 K ≤ M₁)
    (hTC : ∀ D : Subgroup (OTwoQuot K), D ≤ imageOTwoQuot K L →
      (D.subgroupOf (imageOTwoQuot K L)).Normal → IsPGroup 3 D →
      ∀ d ∈ D, ∀ l ∈ imageOTwoQuot K L, Commute d l) {r : ℕ}
    (Lb : Fin r → Subgroup G)
    (hLb : ∀ i, IsBlock2 K (Lb i) ∧ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3)
    (hprod : ∀ h ∈ K, ∃ m ∈ M₁, ∃ x : Fin r → G,
      (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod) : L ≤ M₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKn : (imageOTwoQuot K L).Normal := by
    have hn : (L.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr hKL
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hKperf : ⁅imageOTwoQuot K L, imageOTwoQuot K L⁆ = imageOTwoQuot K L := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    have : Group.IsPerfect ↥(L.subgroupOf K) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLK).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLK).symm.surjective
    have : Group.IsPerfect ↥(imageOTwoQuot K L) :=
      Group.IsPerfect.ofSurjective
        (f := (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)).subgroupMap (L.subgroupOf K))
        ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)).subgroupMap_surjective _)
    exact Subgroup.isPerfect_iff.mp this
  have hB3 : ∀ i, IsPGroup 3 (imageOTwoQuot K (Lb i)) := by
    intro i
    obtain ⟨e⟩ :=
      C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (IsBlock2.isSubnormal (hLb i).1)
    have hcard : Nat.card ↥(imageOTwoQuot K (Lb i)) = 3 ^ 1 :=
      ((Nat.card_congr e.toEquiv).symm.trans (hLb i).2).trans (pow_one 3).symm
    exact IsPGroup.of_card hcard
  have hBsub : ∀ i, (imageOTwoQuot K (Lb i)).IsSubnormal := fun i =>
    (hLb i).1.2.2.map (QuotientGroup.mk'_surjective _)
  have hBQ : ∀ i, imageOTwoQuot K (Lb i) ≤ pCoreOf 3 (⊤ : Subgroup (OTwoQuot K)) := by
    intro i
    have hsub : IsSubnormal (imageOTwoQuot K (Lb i)) ⊤ := A3.subnormal_top_iff.mpr (hBsub i)
    have h1 : imageOTwoQuot K (Lb i) ≤ pCoreOf 3 (imageOTwoQuot K (Lb i)) :=
      le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer (hB3 i)
    exact h1.trans (A4.pCoreOf_le_of_subnormal 3 hsub)
  have hQn : (pCoreOf 3 (⊤ : Subgroup (OTwoQuot K))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 3 ⊤))
  have hx : ∀ x ∈ imageOTwoQuot K L, ∃ m ∈ imageOTwoQuot K M₁,
      ∃ b : Fin r → OTwoQuot K, (∀ i, b i ∈ imageOTwoQuot K (Lb i)) ∧
        x = m * (List.ofFn b).prod := by
    intro x hx
    obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    obtain ⟨m, hm, xs, hxs, hlm⟩ := hprod l hl
    have hxsK : ∀ i, xs i ∈ K := fun i => (hLb i).1.2.1 (hxs i)
    refine ⟨QuotientGroup.mk ⟨m, hM₁K hm⟩, mem_imageOTwoQuot_iff.mpr ⟨m, hM₁K hm, hm, rfl⟩,
      fun i => QuotientGroup.mk ⟨xs i, hxsK i⟩,
      fun i => mem_imageOTwoQuot_iff.mpr ⟨xs i, hxsK i, hxs i, rfl⟩, ?_⟩
    have h1 : (⟨l, hl⟩ : ↥K) =
        ⟨m, hM₁K hm⟩ * (List.ofFn fun i => (⟨xs i, hxsK i⟩ : ↥K)).prod := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubmonoidClass.coe_list_prod, List.map_ofFn]
      exact hlm
    rw [h1, QuotientGroup.mk_mul]
    congr 1
    have := map_list_prod (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))
      (List.ofFn fun i => (⟨xs i, hxsK i⟩ : ↥K))
    rw [List.map_ofFn] at this
    exact this
  have hle := He10.le_of_forall_eq_mul_prod_of_commute hKperf
    (pCoreOf_isPGroup 3 (⊤ : Subgroup (OTwoQuot K)))
    (fun i => imageOTwoQuot K (Lb i)) hBQ
    (fun i => commute_of_perfect_normal' hKperf
      (pCoreOf_isPGroup 3 (⊤ : Subgroup (OTwoQuot K))) (hBQ i) hTC) hx
  intro l hl
  have hlK : l ∈ K := hLK hl
  exact mem_of_mk_mem_imageOTwoQuot hOK
    (hle (mem_imageOTwoQuot_iff.mpr ⟨l, hlK, hl, rfl⟩) :
      (QuotientGroup.mk ⟨l, hlK⟩ : OTwoQuot K) ∈ imageOTwoQuot K M₁)

end Tools

section Main

variable {G : Type} [Group G] [Finite G]

theorem e623CCompBlock_of (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h621 : E621Stmt)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) : E623CCompBlock := by
  intro G _ _ T M V U₀ X hV h hm hU₀V hq2 hU₀Γ hX hXq hXM hCVX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  set H₀ := Subgroup.centralizer (U₀ : Set G) with hH₀def
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  have hQ2 : IsPGroup 2 Q := h.isPGroup_Q
  have hQH₀ : IsSylowTwoOf Q H₀ := e6_5_one h hU₀Γ
  have hO₀ : oddCoreIn H₀ = ⊥ := h621 G T M V U₀ hV h (Or.inr hm) hU₀V hU₀Γ.2.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hpc₀ : pCoreOf 2 H₀ ≠ ⊥ := by
    intro h0
    apply hU₀Γ.2.1
    refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_ (Subgroup.centralizer_le_normalizer _)
      (h.isPGroup_V.to_le hU₀V))
    exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hU₀V hw') _ (hU₀V hw)
  have hQM : Q ≤ M := inf_le_left.trans h.inM.2
  set Y := conjClosure X Q with hYdef
  set K := Y ⊔ Q with hKdef
  have hXH₀ : X ≤ H₀ := le_of_mem_cComp hX
  have hYH₀ : Y ≤ H₀ := conjClosure_le_of_le hXH₀ hQH₀.1
  have hKH₀ : K ≤ H₀ := sup_le hYH₀ hQH₀.1
  have hH₀Y : H₀ ≤ Subgroup.normalizer (Y : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hq.1 h37 h38 hpc₀ hQH₀ hX
  have hQY : Q ≤ Subgroup.normalizer (Y : Set G) := hQH₀.1.trans hH₀Y
  have hYsn : IsSubnormal Y H₀ :=
    A3.subnormal_of_normal hYH₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hYH₀).2 hH₀Y)
  have hQK : IsSylowTwoOf Q K := A4.isSylowTwoOf_mono hQH₀ le_sup_right hKH₀
  have hK : CharTwo K := charTwo_conjClosure_sup hq.1 h37 h38 hpc₀ hQH₀ hO₀ hX hXq
  have hKne : pCoreOf 2 K ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hK
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQK.1.trans h1)
  have hsq : IsSQTKIn K :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hKne,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hKne⟩
  have hcgs : cgsIn K Q ≤ K ⊓ M := by
    have h1 : cgsIn K Q ≤ cgsIn H₀ Q :=
      iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
        inf_le_inf_right _ hKH₀
    have h2 : cgsIn K Q ≤ K :=
      iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left
    exact le_inf h2 ((h1.trans (e6_5_two h hU₀Γ).1).trans inf_le_right)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 G K Q (K ⊓ M) hsq hK hQK hcgs inf_le_left
  by_cases hqt : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  ·
    obtain ⟨i, hi⟩ := hqt
    set B := Lb i with hBdef
    have hBi : IsBlock2 K B := (hLb i).1.1
    have hBc : B ∈ cComp K := L238.mem_cComp_of_isBlock2 hBi hi
    have hBY : B ≤ Y := C2Push.le_of_perfect_le_sup hQ2 hQY (perfect_of_mem_cComp hBc) hBi.2.1
    have hBH₀ : B ∈ cComp H₀ :=
      cComp_mem_of_subnormal hYsn (cComp_mem_of_le hBc hBY le_sup_left)
    obtain ⟨q₀, hq₀, hBeq⟩ := exists_eq_map_conj_of_mem_cComp hq.1 h37 hpc₀ hQH₀.1 hX hBH₀ hBY
    have hconj : X.map (MulAut.conj q₀).toMonoidHom = CFSG.conjugate X q₀⁻¹ := by
      show _ = X.map (MulAut.conj q₀⁻¹⁻¹).toMonoidHom
      rw [inv_inv]
    have hXeq : X = CFSG.conjugate B q₀ := by
      rw [hBeq, hconj, BenderBranch.conjugate_conjugate, inv_mul_cancel,
        BenderBranch.conjugate_one]
    have hq₀K : q₀ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (hQK.1 hq₀)
    have hXK : IsBlock2 K X := by
      rw [hXeq]
      have h1 := Setup.Campbell.isBlock2_map_conj hBi q₀⁻¹
      have h2 : K.map (MulAut.conj q₀⁻¹).toMonoidHom = K :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hq₀K
      rw [h2] at h1
      exact h1
    have hq₀V : q₀ ∈ Subgroup.normalizer (V : Set G) := h.normal hq₀.1
    have hq₀U₀ : q₀⁻¹ ∈ Subgroup.normalizer (U₀ : Set G) :=
      Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hU₀V hq₀.2))
    have hCVB : V ⊓ Subgroup.centralizer (B : Set G) = U₀ := by
      rw [hBeq, hconj, inf_centralizer_conjugate (Subgroup.inv_mem _ hq₀V), hCVX]
      exact BenderBranch.conjugate_eq_iff_mem_normalizer.2 hq₀U₀
    have hU₀4 : U₀.relIndex V = 4 := by
      rw [E3.relIndex_eq_two_pow h.isPGroup_V U₀, hq2]
      norm_num
    have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hBc
    have hBM : ¬ B ≤ M := by
      intro hle
      apply hXM
      rw [hXeq]
      intro x hx
      rw [BenderBranch.mem_conjugate_iff] at hx
      have h1 := hle hx
      have h2 : q₀⁻¹ * (q₀ * x * q₀⁻¹) * q₀ ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem (hQM hq₀)) h1) (hQM hq₀)
      simpa [mul_assoc] using h2
    have hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
      (e6_5_three h hU₀Γ).2 ⟨hKH₀ hg.1, hg.2⟩
    have hVB : ¬ V ≤ Subgroup.centralizer (B : Set G) := by
      intro hle
      have h1 : V ⊓ Subgroup.centralizer (B : Set G) = V := inf_eq_left.2 hle
      rw [hCVB] at h1
      rw [h1, Subgroup.relIndex_self] at hU₀4
      omega
    rcases (hLb i).1.2 with ⟨n, hn, hlin⟩ | h3 | h5
    ·
      obtain ⟨hidx, -⟩ := lin2_block_torus hV h.le hQK hQM hKN hK hBi hn hlin (hLb i).2.1 hVB
      rw [hCVB, hU₀4] at hidx
      have hn2 : n = 2 := by
        have h1 : 2 ^ 2 = 2 ^ n := by rw [← hidx]; norm_num
        exact (Nat.pow_right_injective le_rfl h1).symm
      subst hn2
      have hlinX : IsLin2Type X 2 := by
        rw [hXeq]
        exact Lin2.IsLin2Type.map_equiv hlin (MulAut.conj q₀⁻¹)
      have hJQ : (thompsonJ Q).map (MulAut.conj q₀⁻¹).toMonoidHom = thompsonJ Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1
          (H13.VolI.mem_normalizer_thompsonJ (Subgroup.le_normalizer (Q.inv_mem hq₀)))
      have hJX : ⁅X, thompsonJ Q⁆ = X := by
        rw [hXeq]
        show ⁅B.map (MulAut.conj q₀⁻¹).toMonoidHom, thompsonJ Q⁆ =
          B.map (MulAut.conj q₀⁻¹).toMonoidHom
        rw [← hJQ, ← Subgroup.map_commutator, (hLb i).2.2]
      have hχX : IsChi0Block K X := ⟨hXK, Or.inl ⟨2, by norm_num, hlinX⟩⟩
      have hBor := H13.VolI.isBorelOfBlock_of_isChi0Block hK hQK (hcgs.trans inf_le_right) hQM
        hχX hJX hXM
      have hXKM : X ⊓ (K ⊓ M) = X ⊓ M := by rw [← inf_assoc, inf_eq_left.2 hXK.2.1]
      exact ⟨K, le_sup_right, hKH₀, hK, hXK, hlinX, hXKM ▸ hBor⟩
    ·
      exact absurd (C2Six.natCard_pCore_quotient_of_isAltType_three h3) hi
    ·
      have h1 := relIndex_le_two_of_alt5 hK hBi h5 hQK h.le_inf_centralizer inf_le_right
      rw [hCVB, hU₀4] at h1
      omega
  ·
    push Not at hqt
    exfalso
    have hXK : X ∈ cComp K := cComp_mem_of_le hX ((le_conjClosure X Q).trans le_sup_left) hKH₀
    have hTC := threeCentral_conjClosure h.qtke h.simple h.nonabelian h36 hq.1 h37 hKne
      le_sup_right hXK
    have hOK : pCoreOf 2 K ≤ K ⊓ M :=
      le_inf (pCoreOf_le 2 K) ((B6.pCoreOf_two_le_of_isSylowTwoOf hQK).trans hQM)
    have hYM := le_of_all_A3_of_threeCentral (L := Y) le_sup_left
      (sup_le Subgroup.le_normalizer hQY) (A3.conjClosure_perfect (perfect_of_mem_cComp hX))
      inf_le_left hOK hTC Lb (fun i => ⟨(hLb i).1.1, hqt i⟩) hprod
    exact hXM ((le_conjClosure X Q).trans (hYM.trans inf_le_right))

theorem e623A5Dichotomy_of_kg (h311 : Theorem311Stmt)
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h621 : E621Stmt) (h68 : E68Stmt)
    (hKG : E623CentA5Block) (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) :
    E623A5Dichotomy :=
  e623A5Dichotomy_of h311 h37 h39 h621 h68 hKG (e623CCompBlock_of h36 h37 h38 h621 hC129)

theorem e623_of_kg (h311 : Theorem311Stmt) (h622 : E622Stmt)
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h621 : E621Stmt) (h68 : E68Stmt)
    (hKG : E623CentA5Block) (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hA3 : E623A3Dichotomy) : E623Stmt :=
  e623_of h311 h622 hC129 hA3
    (e623A5Dichotomy_of_kg h311 h36 h37 h38 h39 h621 h68 hKG hC129)

end Main

end E6

end CFSG.Quasithin
