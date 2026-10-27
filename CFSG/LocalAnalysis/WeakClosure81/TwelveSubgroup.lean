module

public import CFSG.GH74.Uniqueness.Bender.Dickson
import CFSG.LieType.SuzukiSubgroups.Input
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.Assembly.LowTwoRank CFSG.ClassicalModels CFSG.ShultStronglyClosedTI
open scoped MatrixGroups

private theorem b12_TwelveSubgroup_isPGroup_of_isElemAbelian {G : Type} [Group G]
    {A : Subgroup G} (hA : IsElemAbelian 2 A) : IsPGroup 2 A := fun a => ⟨1, by
  have h : a ^ 2 = 1 := Subtype.ext (hA.2 a a.2)
  simpa using h⟩

private theorem b12_TwelveSubgroup_isElemAbelian_of_le {G : Type} [Group G] {A B : Subgroup G}
    (h : A ≤ B) (hB : IsElemAbelian 2 B) : IsElemAbelian 2 A := by
  have hcommB : ∀ a b : ↥B, (a : G) * b = (b : G) * a := fun a b =>
    congrArg Subtype.val (hB.1.is_comm.comm a b)
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => hB.2 x (h hx)⟩
  exact hcommB ⟨a.1, h a.2⟩ ⟨b.1, h b.2⟩

theorem exists_four_subgroup {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (h4 : 4 ≤ Nat.card A) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  have hA2 : IsPGroup 2 A := b12_TwelveSubgroup_isPGroup_of_isElemAbelian hA
  obtain ⟨r, hr⟩ := hA2.exists_card_eq
  have hr2 : 2 ≤ r := by
    have hle : 2 ^ 2 ≤ 2 ^ r := by
      calc 2 ^ 2 = 4 := by norm_num
        _ ≤ Nat.card A := h4
        _ = 2 ^ r := hr
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hle
  have hdvd : 2 ^ 2 ∣ Nat.card ↥A := by
    rw [hr]
    exact pow_dvd_pow 2 hr2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 2 hdvd
  refine ⟨K.map A.subtype, Subgroup.map_subtype_le K,
    b12_TwelveSubgroup_isElemAbelian_of_le (Subgroup.map_subtype_le K) hA, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
  norm_num

theorem rankOne_benderType_psl {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL 2 2 n Y) : BenderType Y n 1 1 := by
  obtain ⟨hadm, K, _, _, hcard, ⟨e⟩⟩ := h
  have hn1 : 1 ≤ n := hadm.2.1
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact hadm.2.2.2.1 (by simp)
  let e' : Y ≃* PSL(2, GaloisField 2 n) :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (projectiveSpecialLinearFieldEquiv (finiteFieldEquivGaloisField K 2 n (by omega) hcard)
        (Fin 2)))
  exact BenderType.linear n hn2 e'

theorem rankOne_benderType_sz {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : CFSG.Quasithin.IsSz n Y) : BenderType Y n 2 1 := by
  obtain ⟨-, a, ha, K, _, _, hn, hcard, ⟨e⟩⟩ := h
  subst hn
  let e' : Y ≃* Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (glaSzEquivNative a ha hcard))
  exact BenderType.suzuki a ha (e'.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))

section RankOne

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem rankOne_exists_benderCore
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) (S : Sylow 2 G) :
    ∃ (i : ℕ) (t : G), BenderCore (2 ^ n) i 1 (S : Subgroup G) t := by
  rcases hG with h | h
  · obtain ⟨t, hc⟩ := (rankOne_benderType_psl h).exists_benderCore S
    exact ⟨1, t, hc⟩
  · obtain ⟨t, hc⟩ := (rankOne_benderType_sz h).exists_benderCore S
    exact ⟨2, t, hc⟩

theorem rankOne_benderCore_of_involution
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) (S : Sylow 2 G) {t : G}
    (ht : t * t = 1) (htS : t ∉ normalizer (S : Set G)) :
    ∃ i : ℕ, BenderCore (2 ^ n) i 1 (S : Subgroup G) t := by
  rcases hG with h | h
  · exact ⟨1, (rankOne_benderType_psl h).benderCore S ht htS⟩
  · exact ⟨2, (rankOne_benderType_sz h).benderCore S ht htS⟩

theorem exists_sylow_of_isBorelIn {B : Subgroup G}
    (hB : CFSG.Quasithin.IsBorelIn (⊤ : Subgroup G) B) :
    ∃ S : Sylow 2 G, B = normalizer (S : Set G) := by
  obtain ⟨S, ⟨-, hS2, hSidx⟩, hBS⟩ := hB
  have hidx : (S.subgroupOf ⊤).index = S.index := by
    show S.relIndex ⊤ = S.index
    exact Subgroup.relIndex_top_right (H := S)
  refine ⟨hS2.toSylow (hidx ▸ hSidx), ?_⟩
  rw [hBS, top_inf_eq]
  exact (congrArg (fun T : Subgroup G => normalizer (T : Set G))
    (IsPGroup.toSylow_coe hS2 (hidx ▸ hSidx))).symm

theorem rankOne_sylow_eq_of_ne_bot
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S S₁ : Sylow 2 G}
    {V : Subgroup G} (hV : V ≠ ⊥) (hVS : V ≤ (S : Subgroup G)) (hVS₁ : V ≤ (S₁ : Subgroup G)) :
    S₁ = S := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  exact hc.sylow_eq_of_ne_bot hV hVS hVS₁

theorem rankOne_normalizer_le_borel
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S : Sylow 2 G}
    {V : Subgroup G} (hV : V ≠ ⊥) (hVS : V ≤ (S : Subgroup G)) :
    normalizer (V : Set G) ≤ normalizer (S : Set G) := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  exact IsStronglyEmbedded.normalizer_le hc.strong (hVS.trans (le_borel _))
    (IsPGroup.to_le S.isPGroup' hVS) hV

private theorem b12_TwelveSubgroup_le_sylow_of_le_normalizer {G : Type} [Group G] [Finite G]
    {S : Sylow 2 G} {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXN : X ≤ normalizer (S : Set G)) : X ≤ (S : Subgroup G) := by
  have hsup : IsPGroup 2 (((S : Subgroup G) ⊔ X : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' S.isPGroup' hX hXN
  have htop : (((S : Subgroup G) ⊔ X : Subgroup G)) = (S : Subgroup G) :=
    S.is_maximal' hsup le_sup_left
  rw [← htop]
  exact le_sup_right

theorem rankOne_conj_not_le_borel
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {B A : Subgroup G}
    (hB : CFSG.Quasithin.IsBorelIn (⊤ : Subgroup G) B) (hAB : A ≤ B) (hA : IsElemAbelian 2 A)
    (hA1 : A ≠ ⊥) {g : G} (hg : g ∉ B) : ¬ A.map (MulAut.conj g).toMonoidHom ≤ B := by
  intro hAgB
  obtain ⟨S, rfl⟩ := exists_sylow_of_isBorelIn hB
  have hA2 : IsPGroup 2 A := b12_TwelveSubgroup_isPGroup_of_isElemAbelian hA
  have hAS : A ≤ (S : Subgroup G) :=
    b12_TwelveSubgroup_le_sylow_of_le_normalizer hA2 hAB
  have hAg2 : IsPGroup 2 (A.map (MulAut.conj g).toMonoidHom) := hA2.map _
  have hAgS : A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) :=
    b12_TwelveSubgroup_le_sylow_of_le_normalizer hAg2 hAgB
  have hAle : A ≤ (((g⁻¹) • S : Sylow 2 G) : Subgroup G) := by
    intro x hx
    rw [mem_sylow_smul_iff g⁻¹ S x]
    have := hAgS (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
    simpa [MulAut.conj_apply] using this
  have hSg : ((g⁻¹) • S : Sylow 2 G) = S :=
    rankOne_sylow_eq_of_ne_bot hG hA1 hAS hAle
  have hginv : g⁻¹ ∈ normalizer (S : Set G) := Sylow.smul_eq_iff_mem_normalizer.mp hSg
  exact hg (by simpa using (normalizer (S : Set G)).inv_mem hginv)

theorem rankOne_elemAbelian_le_rootCenter
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S : Sylow 2 G}
    {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hA : IsElemAbelian 2 A) :
    A ≤ rootCenter (S : Subgroup G) := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  exact hc.elemAbelian_le_rootCenter hAS (fun x hx => by simpa [sq] using hA.2 x hx)

theorem rankOne_card_rootCenter
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) (S : Sylow 2 G) :
    Nat.card (rootCenter (S : Subgroup G)) = 2 ^ n := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  exact hc.card_center

theorem rankOne_card_elemAbelian_le
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S : Sylow 2 G}
    {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ^ n ∧ (Nat.card A = 2 ^ n → A = rootCenter (S : Subgroup G)) := by
  have hle := rankOne_elemAbelian_le_rootCenter hG hAS hA
  have hcard := rankOne_card_rootCenter hG S
  refine ⟨hcard ▸ Subgroup.card_le_of_le hle, fun hAeq => ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hAeq])

private theorem b12_TwelveSubgroup_eq_bot_of_odd_of_sq_eq_one {G : Type} [Group G]
    {H : Subgroup G} (hodd : Odd (Nat.card H)) (hsq : ∀ x ∈ H, x * x = 1) : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx2 : x * x = 1 := hsq x hx
  have hdvd : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx2])
  have hoddx : Odd (orderOf x) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard H hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hoddx
    exact absurd hoddx (by norm_num)

private theorem b12_TwelveSubgroup_card_le_two_of_le_sup_zpowers {G : Type} [Group G]
    {C : Subgroup G} {w : G} (hw : w * w = 1)
    (hwinv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) (hCodd : Odd (Nat.card C))
    {E : Subgroup G} (hE : E ≤ C ⊔ Subgroup.zpowers w)
    (hEsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 := by
  have hwC : w ∈ C ⊔ Subgroup.zpowers w :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hsup_eq : C ⊔ Subgroup.zpowers w = Subgroup.closure ((C : Set G) ∪ {w}) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.closure_union, Subgroup.closure_eq]
  have hP : ∀ x ∈ C ⊔ Subgroup.zpowers w, x * w ∈ C ∨ x ∈ C := by
    intro x hx
    have hx' : x ∈ Subgroup.closure ((C : Set G) ∪ {w}) := hsup_eq ▸ hx
    refine Subgroup.closure_induction (p := fun y _ => y * w ∈ C ∨ y ∈ C) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      rcases hy with hyC | hyw
      · exact Or.inr hyC
      · rw [Set.mem_singleton_iff] at hyw
        subst hyw
        exact Or.inl (by rw [hw]; exact C.one_mem)
    · exact Or.inr C.one_mem
    · intro y z _ _ hy hz
      rcases hy with hyw | hyC
      · rcases hz with hzw | hzC
        · right
          have hy' : y = (y * w) * w := by rw [mul_assoc, hw, mul_one]
          have hz' : z = (z * w) * w := by rw [mul_assoc, hw, mul_one]
          rw [hy', hz']
          have heq : ((y * w) * w) * ((z * w) * w) = (y * w) * (w * (z * w) * w⁻¹) := by
            rw [inv_eq_of_mul_eq_one_right hw]; group
          rw [heq]
          exact C.mul_mem hyw (hwinv (z * w) hzw ▸ C.inv_mem hzw)
        · left
          have hy' : y = (y * w) * w := by rw [mul_assoc, hw, mul_one]
          rw [hy']
          have heq : ((y * w) * w) * z * w = (y * w) * (w * z * w⁻¹) := by
            rw [inv_eq_of_mul_eq_one_right hw]; group
          rw [heq]
          exact C.mul_mem hyw (hwinv z hzC ▸ C.inv_mem hzC)
      · rcases hz with hzw | hzC
        · left
          have hz' : z = (z * w) * w := by rw [mul_assoc, hw, mul_one]
          rw [hz']
          have heq : y * ((z * w) * w) * w = y * (z * w) * (w * w) := by group
          rw [heq, hw, mul_one]
          exact C.mul_mem hyC hzw
        · right
          exact C.mul_mem hyC hzC
    · intro y _ hy
      rcases hy with hyw | hyC
      · left
        have hy' : y = (y * w) * w := by rw [mul_assoc, hw, mul_one]
        have hwy : w * y ∈ C := by
          have h := hwinv (y * w) hyw
          rw [hy']
          have heq : w * ((y * w) * w) = w * (y * w) * w⁻¹ := by
            rw [inv_eq_of_mul_eq_one_right hw]
            simp only [mul_assoc]
          rw [heq]
          exact h ▸ C.inv_mem hyw
        have heq2 : y⁻¹ * w = (w * y)⁻¹ := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hw]
        rw [heq2]
        exact C.inv_mem hwy
      · right
        exact C.inv_mem hyC
  have hdvd : C.relIndex (C ⊔ Subgroup.zpowers w) ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    exact ⟨w, hwC, fun b hb => hP b hb⟩
  have hne : C.relIndex (C ⊔ Subgroup.zpowers w) ≠ 0 := fun h0 => by
    rw [h0] at hdvd
    norm_num at hdvd
  have hle2 : C.relIndex (C ⊔ Subgroup.zpowers w) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hEC : E ⊓ C = ⊥ := by
    refine b12_TwelveSubgroup_eq_bot_of_odd_of_sq_eq_one ?_ ?_
    · exact Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_le inf_le_right)
    · intro x hx
      exact hEsq x (Subgroup.mem_inf.mp hx).1
  have hcard : Nat.card E = C.relIndex E := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := E)
    rw [inf_comm, hEC, Subgroup.card_bot, mul_one] at h
    exact h.symm
  calc Nat.card E = C.relIndex E := hcard
    _ ≤ C.relIndex (C ⊔ Subgroup.zpowers w) := Subgroup.relIndex_le_of_le_right hE hne
    _ ≤ 2 := hle2

theorem rankOne_subgroup_cases
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {J E : Subgroup G}
    (hJ : J ≠ ⊤) (hEJ : E ≤ J) (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    (∃ S : Sylow 2 G, J ≤ normalizer (S : Set G)) ∨
      ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧ k < n ∧
        ((CFSG.Quasithin.IsPSL 2 2 n G ∧ CFSG.Quasithin.IsPSL 2 2 k ↥J) ∨
          (CFSG.Quasithin.IsSz n G ∧ CFSG.Quasithin.IsSz k ↥J)) := by
  rcases hG with hPSL | hSz
  · have hB : BenderType G n 1 1 := rankOne_benderType_psl hPSL
    have hn1 : 1 ≤ n := by
      obtain ⟨hadm, -⟩ := hPSL
      exact hadm.2.1
    rcases hB.lemma_3_7 J hJ with hbor | htor | hsub
    · obtain ⟨Q, hQ⟩ := hbor
      exact Or.inl ⟨Q, hQ⟩
    · exfalso
      obtain ⟨N, hN, hJN⟩ := htor
      obtain ⟨x, w, hx1, hxodd, hw2, hcyc, hCcard, hwinv, hNsup, -⟩ := hN
      have hEsup : E ≤ centralizer ({x} : Set G) ⊔ Subgroup.zpowers w := by
        rw [← hNsup]
        exact hEJ.trans hJN
      have hEsq : ∀ y ∈ E, y * y = 1 := fun y hy => by
        simpa [sq] using hE.2 y hy
      have hCodd : Odd (Nat.card ↥(centralizer ({x} : Set G))) := by
        rcases hCcard with h | h
        · rw [h]; exact odd_two_pow_sub_one n hn1
        · rw [h]; exact odd_two_pow_add_one n hn1
      have hEscard : Nat.card E ≤ 2 :=
        b12_TwelveSubgroup_card_le_two_of_le_sup_zpowers hw2 hwinv hCodd hEsup hEsq
      omega
    · right
      obtain ⟨n₀, m, hn₀1, hm2, hnm, ⟨φ⟩⟩ := hsub
      have hn₀ne1 : n₀ ≠ 1 := by
        intro h1
        subst h1
        have hdvd : 4 ∣ Nat.card J := by
          rw [← h4]
          exact Subgroup.card_dvd_of_le hEJ
        have h6 : Nat.card J = 6 := by
          rw [Nat.card_congr φ.toEquiv, card_psl2_even 1 le_rfl]
          norm_num
        exact (by norm_num : ¬ (4 ∣ 6)) (h6 ▸ hdvd)
      have hn₀2 : 2 ≤ n₀ := by omega
      have hPSLJ : CFSG.Quasithin.IsPSL 2 2 n₀ ↥J := by
        change StatedClassicalModel ↥J .PSL 2 2 n₀
        unfold StatedClassicalModel
        refine ⟨?_, GaloisField 2 n₀, inferInstance, inferInstance, ?_, ?_⟩
        · unfold StatedLieAdmissible
          refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
          · intro hcon
            have hk : 2 ^ n₀ = 2 := by simpa using congrArg Prod.snd hcon
            have hle : 2 ^ 2 ≤ 2 ^ n₀ := Nat.pow_le_pow_right (by norm_num) hn₀2
            rw [hk] at hle
            norm_num at hle
          · intro hcon
            have hk : 2 ^ n₀ = 3 := by simpa using congrArg Prod.snd hcon
            have hle : 2 ^ 2 ≤ 2 ^ n₀ := Nat.pow_le_pow_right (by norm_num) hn₀2
            rw [hk] at hle
            norm_num at hle
        · exact GaloisField.card 2 n₀ (by omega)
        · exact ⟨φ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 n₀))⟩
      refine ⟨n₀, hn₀2, ⟨m, hnm⟩, ?_, Or.inl ⟨hPSL, hPSLJ⟩⟩
      rw [hnm]
      nlinarith [hn₀2, hm2]
  · rcases CFSG.LieType.SuzukiSubgroups.suzukiSubgroupInput_holds n G hSz J hJ
        ⟨E, hEJ, hE, h4⟩ with hbor | hsub
    · exact Or.inl hbor
    · right
      obtain ⟨k, hkdn, hklt, hSzk⟩ := hsub
      have hk2 : 2 ≤ k := by
        obtain ⟨-, a, ha, K, -, -, hk, -, -⟩ := hSzk
        omega
      exact ⟨k, hk2, hkdn, hklt, Or.inr ⟨hSz, hSzk⟩⟩

theorem rankOne_isBorelIn_subgroupOf
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {B A L : Subgroup G}
    (hB : CFSG.Quasithin.IsBorelIn (⊤ : Subgroup G) B) (hAB : A ≤ B) (hA : IsElemAbelian 2 A)
    (hA1 : A ≠ ⊥) (hAL : A ≤ L) :
    CFSG.Quasithin.IsBorelIn (⊤ : Subgroup ↥L) (B.subgroupOf L) := by
  obtain ⟨S₀, rfl⟩ := exists_sylow_of_isBorelIn hB
  have hA2 : IsPGroup 2 A := b12_TwelveSubgroup_isPGroup_of_isElemAbelian hA
  have hAS₀ : A ≤ (S₀ : Subgroup G) :=
    b12_TwelveSubgroup_le_sylow_of_le_normalizer hA2 hAB
  have hA2L : IsPGroup 2 (A.subgroupOf L) := hA2.comap_subtype
  obtain ⟨Q, hAQ⟩ := hA2L.exists_le_sylow
  have hQ'2 : IsPGroup 2 (Q.map L.subtype) := (Q.isPGroup').map L.subtype
  obtain ⟨S'', hQ'S''⟩ := hQ'2.exists_le_sylow
  have hAQ' : A ≤ Q.map L.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAL]
    exact Subgroup.map_mono hAQ
  have hS''eq : S'' = S₀ :=
    rankOne_sylow_eq_of_ne_bot hG hA1 hAS₀ (hAQ'.trans hQ'S'')
  have hQ'S₀ : Q.map L.subtype ≤ (S₀ : Subgroup G) := by
    rw [hS''eq] at hQ'S''
    exact hQ'S''
  have hQeq : ((S₀ : Subgroup G) ⊓ L).subgroupOf L = (Q : Subgroup ↥L) := by
    refine Q.is_maximal' ?_ ?_
    · exact (IsPGroup.to_le S₀.isPGroup' inf_le_left).comap_subtype
    · intro q hq
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hQ'S₀ (Subgroup.mem_map_of_mem L.subtype hq), q.2⟩
  have hnorm : Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) =
      (Subgroup.normalizer (((S₀ : Subgroup G) ⊓ L) : Set G)).subgroupOf L := by
    rw [← hQeq]
    exact (Subgroup.subgroupOf_normalizer_eq (H := (S₀ : Subgroup G) ⊓ L) (N := L)
      inf_le_right).symm
  have hsubLe : (Subgroup.normalizer (S₀ : Set G)).subgroupOf L ≤
      Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
    rw [hnorm]
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    have hxS₀ : (x : G) ∈ Subgroup.normalizer (S₀ : Set G) := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_set_normalizer_iff] at hxS₀ ⊢
    intro y
    have hconjL : ((x : G) * y * (x : G)⁻¹ ∈ L) ↔ y ∈ L := by
      constructor
      · intro hy
        have h1 : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem x.2) hy) x.2
        simpa [mul_assoc] using h1
      · intro hy
        exact L.mul_mem (L.mul_mem x.2 hy) (L.inv_mem x.2)
    exact ⟨fun hy => ⟨(hxS₀ y).mp hy.1, hconjL.mpr hy.2⟩,
      fun hy => ⟨(hxS₀ y).mpr hy.1, hconjL.mp hy.2⟩⟩
  have hVne : ((S₀ : Subgroup G) ⊓ L) ≠ ⊥ := by
    intro hbot
    apply hA1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have : a ∈ (S₀ : Subgroup G) ⊓ L := ⟨hAS₀ ha, hAL ha⟩
    rw [hbot] at this
    exact this
  have hnormLe : Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) ≤
      (Subgroup.normalizer (S₀ : Set G)).subgroupOf L := by
    rw [hnorm]
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    have hxN : (x : G) ∈ Subgroup.normalizer (((S₀ : Subgroup G) ⊓ L) : Set G) :=
      Subgroup.mem_subgroupOf.mp hx
    exact rankOne_normalizer_le_borel hG hVne inf_le_left hxN
  refine ⟨(Q : Subgroup ↥L), ⟨le_top, Q.isPGroup', ?_⟩, ?_⟩
  · intro h2dvd
    have hidx : ((Q : Subgroup ↥L).subgroupOf ⊤).index = (Q : Subgroup ↥L).index := by
      show (Q : Subgroup ↥L).relIndex ⊤ = (Q : Subgroup ↥L).index
      exact Subgroup.relIndex_top_right (H := (Q : Subgroup ↥L))
    exact Sylow.not_dvd_index Q (hidx ▸ h2dvd)
  · rw [top_inf_eq]
    exact le_antisymm hsubLe hnormLe

end RankOne

end CFSG.LocalAnalysis.WeakClosure81
