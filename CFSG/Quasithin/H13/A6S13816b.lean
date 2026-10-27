module

public import CFSG.Quasithin.H13.A6S13816a
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Two
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem kst_equiv (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(S.KSt H K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  set φ := actH hV₁ hIH with hφ
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hK' : S.KSt H K = (K.subgroupOf H).map φ := autOn_tilde_eq_map_actH hV₁ hIH hKH
  let f : ↥K →* ↥(S.KSt H K) :=
    { toFun := fun k => ⟨φ ⟨k, hKH k.2⟩, by rw [hK']; exact ⟨_, Subgroup.mem_subgroupOf.2 k.2, rfl⟩⟩
      map_one' := Subtype.ext (by
        show φ 1 = 1
        exact map_one φ)
      map_mul' := fun a b => Subtype.ext (by
        show φ (⟨(a : G), hKH a.2⟩ * ⟨(b : G), hKH b.2⟩) = φ ⟨a, hKH a.2⟩ * φ ⟨b, hKH b.2⟩
        rw [map_mul]) }
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hK'] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  have hfker : f.ker = CFSG.pCore 2 ↥K := by
    apply le_antisymm
    ·
      set N : Subgroup ↥K := (pCoreOf 2 H).subgroupOf K with hN
      have hNn : N.Normal := by
        refine ⟨fun n hn k => ?_⟩
        rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
        have hkH : (k : G) ∈ H := hKH k.2
        have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hkH) n).1 hn
        simpa using this
      have hNp : IsPGroup 2 N := by
        intro x
        have hx : ((x : ↥K) : G) ∈ pCoreOf 2 H := x.2
        obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, hx⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
      intro x hx
      have hx1 : φ ⟨x, hKH x.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      have hxN : x ∈ N := by
        rw [hN, Subgroup.mem_subgroupOf]
        exact (hker _).1 hx1
      exact le_pCore 2 hNn hNp hxN
    · intro x hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show φ ⟨x, hKH x.2⟩ = 1
      rw [hker]
      have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by assumption
      exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) ⟨x, hx', rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

theorem sqtkGroup_of_mem_Hz {H : Subgroup G} (hH : H ∈ S.Hz) : SQTKGroup ↥H := by
  obtain ⟨hk, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian
    (T := T) ⟨le_sup_right.trans hH.1.1, hH.1.2⟩
  exact ⟨hq, hk⟩

omit [Finite G] S in
theorem pCoreOf_subgroupOf_eq (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K

theorem hypF918_K0 (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) :
    (K ⊔ T) ⊔ S.L1 ∈ S.Hz ∧ (K ⊔ T) ⊔ S.L1 ≤ H ∧
      HypF918 T V L (fsuV1 T V) S.V3 ((K ⊔ T) ⊔ S.L1) K := by
  set H₀ := (K ⊔ T) ⊔ S.L1 with hH₀
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hH₀z : H₀ ∈ S.Hz := (S.lem13812_one h139 h37 h38 hH hK).2
  have hH₀H : H₀ ≤ H := sup_le (sup_le hKH hTH) (le_sup_left.trans hH.1.1)
  have hK₀ : K ∈ cComp H₀ := cComp_mem_of_le hK (le_sup_left.trans le_sup_left) hH₀H
  have hF := hS.hF H₀ hH₀z
  have hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf_eq K).symm)
      (S.isQuasisimple_modO2 h36 h139 h1334 h13 hS hH hK)
  have hTsyl : IsSylowTwoOf T H₀ :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow (le_sup_right.trans le_sup_left)
  have hnorm : H₀ ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
      hH₀z.1.2 hTsyl hK₀
  refine ⟨hH₀z, hH₀H,
    { toHypF98 := hF
      K_cComp := hK₀
      K_quasisimple := hq
      H_eq := ?_
      K₀_normal := hnorm }⟩
  rw [hF.toHypF91.LT_inf_H]
  have hTH₀ : T ≤ H₀ := le_sup_right.trans le_sup_left
  have hKH₀ : K ≤ H₀ := le_sup_left.trans le_sup_left
  have hL1H₀ : S.L1 ≤ H₀ := le_sup_right
  have hK₀H₀ : conjClosure K T ≤ H₀ := conjClosure_le fun t ht k hk =>
    H₀.mul_mem (H₀.mul_mem (hTH₀ ht) (hKH₀ hk)) (H₀.inv_mem (hTH₀ ht))
  apply le_antisymm
  · refine sup_le (sup_le ?_ (le_sup_right.trans le_sup_right)) (le_sup_left.trans le_sup_right)
    exact (le_conjClosure K T).trans le_sup_left
  · exact sup_le hK₀H₀ (sup_le hL1H₀ hTH₀)

theorem fiveShape_of_ne
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K) :
    FiveShape (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨hH₀z, -, hF⟩ := S.hypF918_K0 h36 h37 h38 h139 h1334 h13 hS hH hK
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h5 := (F918_5' hF (S.sqtkGroup_of_mem_Hz hH₀z) hne hV₁I hIU W hW hirrU hD36 hD37 hD321
    hI5 h37 h38).1
  obtain ⟨e⟩ := L1295B.nonempty_mulEquiv_autIH hF
  exact fiveShape_congr e.symm h5

end Setting4

@[expose] def Case13816L32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, conjClosure K T ≠ K → H = (K ⊔ T) ⊔ S.L1 →
      ¬ IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Case13816L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, conjClosure K T ≠ K → H = (K ⊔ T) ⊔ S.L1 →
      ¬ ((∃ n, IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) ∨ IsAlt 5 (↥K ⧸ CFSG.pCore 2 ↥K))

@[expose] def Case13816SzPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, conjClosure K T ≠ K → H = (K ⊔ T) ⊔ S.L1 →
      ¬ ∃ n, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Case13816SzNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, H ≤ Subgroup.normalizer (K : Set G) → H = (K ⊔ T) ⊔ S.L1 →
      ¬ ∃ n, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K)

theorem lem13816_of_cases
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (hL32 : Case13816L32) (hL2 : Case13816L2)
    (hSzP : Case13816SzPair) (hSzN : Case13816SzNormal) : Lem13816 := by
  intro G _ _ T L V S hS H hH K hK
  obtain ⟨hH₀z, hH₀H, hF⟩ := S.hypF918_K0 h36 h37 h38 h139 h1334 h13 hS hH hK
  have hK₀ : K ∈ cComp ((K ⊔ T) ⊔ S.L1) := hF.K_cComp
  have hKK : conjClosure K T = K := by
    by_contra hne
    rcases S.fiveShape_of_ne h36 h37 h38 hD36 hD37 hD321 hI5 h139 h1334 h13 hS hH hK hne with
      ⟨n, hn⟩ | ⟨n, hn⟩ | h | h
    · exact hL2 G T L V S hS _ hH₀z K hK₀ hne rfl (Or.inl ⟨n, hn⟩)
    · exact hSzP G T L V S hS _ hH₀z K hK₀ hne rfl ⟨n, hn⟩
    · exact hL2 G T L V S hS _ hH₀z K hK₀ hne rfl (Or.inr h)
    · exact hL32 G T L V S hS _ hH₀z K hK₀ hne rfl h
  have hTsyl : IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow (le_sup_right.trans hH.1.1)
  have hKN : H ≤ Subgroup.normalizer (K : Set G) := by
    have := normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
      hH.1.2 hTsyl hK
    rwa [hKK] at this
  refine ⟨⟨hKN, ?_⟩, ?_⟩
  · have e : (K ⊔ S.L1) ⊔ T = (K ⊔ T) ⊔ S.L1 := by
      rw [sup_assoc, sup_comm S.L1 T, ← sup_assoc]
    rw [e]
    exact hH₀z
  · rintro ⟨n, hn⟩
    obtain ⟨e1⟩ := S.kst_equiv hS hH hK
    have hN₀ : (K ⊔ T) ⊔ S.L1 ≤ Subgroup.normalizer (K : Set G) := by
      have := hF.K₀_normal
      rwa [hKK] at this
    exact hSzN G T L V S hS _ hH₀z K hK₀ hN₀ rfl ⟨n, isSz_congr e1.symm hn⟩

end CFSG.Quasithin.H13.A6

