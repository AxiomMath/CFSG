module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem424N
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.A4
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem le_center_or_eq_top_of_isQuasisimple {X : Type*} [Group X]
    (hX : CFSG.IsQuasisimple X) (N : Subgroup X) [N.Normal] :
    N ≤ Subgroup.center X ∨ N = ⊤ := by
  have : Group.IsPerfect X := hX.1
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
  have hnormal : (N.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hker := N.map_eq_bot_iff.mp hbot
    rwa [QuotientGroup.ker_mk'] at hker
  · right
    have hsup : N ⊔ Subgroup.center X = ⊤ := by
      have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center X)) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : _root_.commutator X ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hderived
    exact eq_top_iff.mpr hderived

theorem eq_top_of_sup_isPGroup_eq_top {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {K P : Subgroup X} [K.Normal] (hP : IsPGroup 2 P) (hKP : K ⊔ P = ⊤) : K = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : P.map (QuotientGroup.mk' K) = ⊤ := by
    have h1 := Subgroup.map_sup K P (QuotientGroup.mk' K)
    rw [hKP, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] at h1
    have h2 : K.map (QuotientGroup.mk' K) = ⊥ :=
      K.map_eq_bot_iff.mpr (QuotientGroup.ker_mk' K).ge
    rw [h2, bot_sup_eq] at h1
    exact h1.symm
  have h2 : IsPGroup 2 (X ⧸ K) := by
    have hP' : IsPGroup 2 ↥(P.map (QuotientGroup.mk' K)) := hP.map _
    rw [hψ] at hP'
    exact hP'.of_equiv Subgroup.topEquiv
  apply QuotientGroup.subgroup_eq_top_of_subsingleton
  by_contra hns
  have : Nontrivial (X ⧸ K) := not_subsingleton_iff_nontrivial.mp hns
  exact Group.IsPerfect.not_isNilpotent (X ⧸ K) h2.isNilpotent

theorem coe_mem_pCoreOf_two_iff {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

theorem commutator_le_pCoreOf_of_normal [Finite G] {L K : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hL : ⁅L, L⁆ = L) (hKL : K ≤ L)
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) (hne : K ≠ L) : ⁅K, L⁆ ≤ pCoreOf 2 L := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have : (K.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLK
  rcases le_center_or_eq_top_of_isQuasisimple hq
      ((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with hc | ht
  · rw [Subgroup.commutator_le]
    intro k hk l hl
    have hk' : (⟨k, hKL hk⟩ : ↥L) ∈ K.subgroupOf L := hk
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨k, hKL hk⟩ ∈ Subgroup.center _ :=
      hc ⟨_, hk', rfl⟩
    have h1 : ⁅(⟨k, hKL hk⟩ : ↥L), ⟨l, hl⟩⁆ ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hmem _).symm
    exact (coe_mem_pCoreOf_two_iff _).mpr h1
  · exfalso
    have hsup : K.subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
      have hcomap :=
        Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (K.subgroupOf L)
      rw [ht, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have htop := eq_top_of_sup_isPGroup_eq_top CFSG.pCore_isPGroup hsup
    refine hne (le_antisymm hKL fun l hl => ?_)
    have hl' : (⟨l, hl⟩ : ↥L) ∈ K.subgroupOf L := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hl'

omit [Group G] in
theorem le_normalizer_of_forall_conj_mem [Group G] {H R : Subgroup G}
    (h : ∀ g ∈ H, ∀ r ∈ R, g * r * g⁻¹ ∈ R) : H ≤ Subgroup.normalizer (R : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => h g hg r hr, fun hr => ?_⟩
  have h1 := h g⁻¹ (H.inv_mem hg) _ hr
  have e : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
  rwa [e] at h1

theorem mem_normalizer_centralizer_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ Subgroup.centralizer (X : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  exact le_normalizer_of_forall_conj_mem key hg

theorem isElemAbelian_two_of_le {A B : Subgroup G} (hAB : A ≤ B) (h : IsElemAbelian 2 B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono h hAB

theorem isPGroup_two_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsPGroup 2 E := CFSG.Open.IsElemAbelian.isPGroup hE

variable [Finite G] {T M L : Subgroup G}

theorem eq_bot_of_commutator_eq_self_of_isPGroup_two {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (h2 : IsPGroup 2 ↥K) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  exact Group.IsPerfect.not_isNilpotent ↥K h2.isNilpotent

theorem conjClosure_le_normalizer_of_hyp421 (h : Hyp4_2_1 G T M L) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) : conjClosure L T ≤ Subgroup.normalizer (L : Set G) := by
  have hLc : L ∈ cComp M := h.mem_cComp h37 h39
  have hO2M : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal h.maxTwoLocal.1
  refine conjClosure_le fun t ht l hl => ?_
  have hLt := map_conj_mem_cComp hLc (h.T_le ht)
  have hmem : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
  by_cases he : L.map (MulAut.conj t).toMonoidHom = L
  · rw [he] at hmem
    exact Subgroup.le_normalizer hmem
  · have hc := (lemma_1_2_1_two h.qtke h.simple h.nonabelian h37 hO2M hLc hLt
      (Ne.symm he)).1
    have hle : L.map (MulAut.conj t).toMonoidHom ≤ Subgroup.normalizer (L : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr
        (hc.trans (inf_le_left.trans (pCoreOf_le 2 L)))
    exact hle hmem

theorem centralizer_commutator_le_pCoreOf (h : Hyp4_2_1 G T M L) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) {V₀ : Subgroup G} (hV₀le : V₀ ≤ conjClosure L T ⊔ T)
    (hV₀N : conjClosure L T ⊔ T ≤ Subgroup.normalizer (V₀ : Set G))
    (hV : ⁅V₀, conjClosure L T⁆ ≠ ⊥) :
    T ⊓ Subgroup.centralizer ((⁅V₀, conjClosure L T⁆ : Subgroup G) : Set G) ≤
      pCoreOf 2 (conjClosure L T ⊔ T) := by
  set Mp := conjClosure L T with hMp
  set V := ⁅V₀, Mp⁆ with hVdef
  set Q := pCoreOf 2 Mp with hQ
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_normalizer_of_hyp421 h h37 h39
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := le_normalizer_conjClosure L T
  have hMpMp : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hTMp
  have hQN : Mp ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    hMpMp.trans (normalizer_le_normalizer_pCoreOf 2 Mp)
  have hperf : ⁅Mp, Mp⁆ = Mp := perfect_conjClosure h.perfect
  have hVN : Mp ⊔ T ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    mem_normalizer_commutator (hV₀N hx) (hMpMp hx)
  have hCN : Mp ⊔ T ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    fun x hx => mem_normalizer_centralizer_of_mem_normalizer (hVN hx)
  have hVL : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hLC
    have hMpC : Mp ≤ Subgroup.centralizer (V : Set G) := conjClosure_le fun t ht l hl =>
      (Subgroup.mem_normalizer_iff.mp (hCN (Subgroup.mem_sup_right ht)) l).mp (hLC hl)
    apply hV
    calc V = ⁅V, Mp⁆ := commutator_eq_commutator_commutator_of_perfect hperf
          (hV₀le.trans hMpMp) (le_sup_left.trans hV₀N)
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer_iff.mp hMpC)
  set N := Mp ⊓ Subgroup.centralizer (V : Set G) with hN
  have hNMp : N ≤ Mp := inf_le_left
  have hMpNN : Mp ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (hCN (Subgroup.mem_sup_left hx))
  have hTNN : T ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    mem_normalizer_inf (hTMp hx) (hCN (Subgroup.mem_sup_right hx))
  have hNL : ⁅N, L⁆ ≤ pCoreOf 2 L := by
    set K := ⁅N, L⁆ with hK
    have hKL : K ≤ L := commutator_le_right_of_le_normalizer (hNMp.trans hMpN)
    have hKN : K ≤ N := commutator_le_left_of_le_normalizer (hLMp.trans hMpNN)
    have hLK : L ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
      mem_normalizer_commutator (hMpNN (hLMp hx)) (Subgroup.le_normalizer hx)
    have hne : K ≠ L := by
      intro he
      refine hVL fun x hx => (hKN ?_).2
      rw [he]
      exact hx
    calc K = ⁅K, L⁆ := commutator_eq_commutator_commutator_of_perfect h.perfect
          (hNMp.trans hMpN) (hLMp.trans hMpNN)
      _ ≤ pCoreOf 2 L := commutator_le_pCoreOf_of_normal h.quasisimple h.perfect hKL hLK hne
  have hO2LQ : pCoreOf 2 L ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLMp)
      (hMpN.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  set X := centralizerSection ⊤ N Q with hX
  have hXN : T ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_forall_conj_mem fun t ht x hx =>
      conj_mem_centralizerSection (Subgroup.le_normalizer (Subgroup.mem_top t)) (hTNN ht)
        (hQN (Subgroup.mem_sup_right ht)) hx
  have hLX : L ≤ X := fun l hl => ⟨Subgroup.mem_top l, hMpNN (hLMp hl),
    hQN (Subgroup.mem_sup_left (hLMp hl)),
    fun n hn => hO2LQ (hNL (Subgroup.commutator_mem_commutator hn hl))⟩
  have hMpX : Mp ≤ X := conjClosure_le fun t ht l hl =>
    (Subgroup.mem_normalizer_iff.mp (hXN ht) l).mp (hLX hl)
  set C' := (Mp ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hC'
  have hC'Mp : C' ≤ Subgroup.normalizer (Mp : Set G) := inf_le_left.trans hMpMp
  have hMpC' : Mp ≤ Subgroup.normalizer (C' : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_left hx))
      (hCN (Subgroup.mem_sup_left hx))
  have hC'N : ⁅C', Mp⁆ ≤ N := le_inf (commutator_le_right_of_le_normalizer hC'Mp)
    ((commutator_le_left_of_le_normalizer hMpC').trans inf_le_right)
  have hC'Q : ⁅C', Mp⁆ ≤ Q := by
    calc ⁅C', Mp⁆ = ⁅⁅C', Mp⁆, Mp⁆ :=
          commutator_eq_commutator_commutator_of_perfect hperf hC'Mp hMpC'
      _ ≤ ⁅N, Mp⁆ := Subgroup.commutator_mono hC'N le_rfl
      _ ≤ Q := by
        rw [Subgroup.commutator_le]
        intro n hn m hm
        exact (hMpX hm).2.2.2 n hn
  have hTsyl : IsSylowTwoOf T (Mp ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  have hQO : Q ≤ pCoreOf 2 (Mp ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Mp).trans le_sup_left) hQN
      (pCoreOf_isPGroup 2 Mp)
  have hQT : Q ≤ T := hQO.trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
  set R' := T ⊓ centralizerSection (Mp ⊔ T) Mp Q with hR'
  have hR'Mp : Mp ≤ Subgroup.normalizer (R' : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg r hr => ⟨?_, ?_⟩
    · have h1 : g * r * g⁻¹ * r⁻¹ ∈ T := hQT (hr.2.2.2.2 g hg)
      have e : g * r * g⁻¹ = (g * r * g⁻¹ * r⁻¹) * r := by group
      rw [e]
      exact T.mul_mem h1 hr.1
    · exact conj_mem_centralizerSection (Subgroup.le_normalizer (Subgroup.mem_sup_left hg))
        (Subgroup.le_normalizer hg) (hQN (Subgroup.mem_sup_left hg)) hr.2
  have hR'T : T ≤ Subgroup.normalizer (R' : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg r hr => ⟨?_, ?_⟩
    · exact T.mul_mem (T.mul_mem hg hr.1) (T.inv_mem hg)
    · exact conj_mem_centralizerSection (Subgroup.le_normalizer (Subgroup.mem_sup_right hg))
        (hTMp hg) (hQN (Subgroup.mem_sup_right hg)) hr.2
  have hR'O : R' ≤ pCoreOf 2 (Mp ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (fun r hr => hr.2.1) (_root_.sup_le hR'Mp hR'T)
      (h.sylow.1.to_le inf_le_left)
  intro x hx
  refine hR'O ⟨hx.1, Subgroup.mem_sup_right hx.1, hTMp hx.1, hQN (Subgroup.mem_sup_right hx.1),
    fun m hm => ?_⟩
  have hxC' : x ∈ C' := ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
  have h1 : ⁅x, m⁆ ∈ Q := hC'Q (Subgroup.commutator_mem_commutator hxC' hm)
  have h2 := Q.inv_mem h1
  have e : ⁅x, m⁆⁻¹ = m * x * m⁻¹ * x⁻¹ := by
    simp only [commutatorElement_def]
    group
  rwa [e] at h2

theorem le_centralizer_omegaOneCenter_of_hyp421 (h : Hyp4_2_1 G T M L) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {V₀ H : Subgroup G} (hV₀le : V₀ ≤ conjClosure L T ⊔ T)
    (hV₀r : IsPrimeReduced 2 (V₀.subgroupOf (conjClosure L T ⊔ T))) (hH : IsHStar T M H)
    (hV : ⁅V₀, conjClosure L T⁆ ≠ ⊥)
    (hFF : ∃ _ : IsMulCommutative ↥⁅V₀, conjClosure L T⁆,
      ¬ IsFFModule (V := ↥⁅V₀, conjClosure L T⁆)
        (autOn (conjClosure L T ⊔ T) ⁅V₀, conjClosure L T⁆)) :
    H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hred : IsTwoReducedIn (conjClosure L T ⊔ T) V₀ :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨hV₀le, hV₀r⟩
  have hkey := centralizer_commutator_le_pCoreOf h h37 h39 hV₀le hred.2.1 hV
  set Mp := conjClosure L T with hMp
  set V := ⁅V₀, Mp⁆ with hVdef
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := le_normalizer_conjClosure L T
  have hMpMp : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hTMp
  have hTsyl : IsSylowTwoOf T (Mp ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  have hVV₀ : V ≤ V₀ := commutator_le_left_of_le_normalizer (le_sup_left.trans hred.2.1)
  have hO2V₀ : pCoreOf 2 (Mp ⊔ T) ≤ Subgroup.centralizer (V₀ : Set G) := by
    refine hred.2.2.2 _ (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) fun d hd => ?_
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (Mp ⊔ T) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have hdk : d ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [hdk]
    exact Subgroup.one_mem _
  have hcent : pCoreOf 2 (Mp ⊔ T) = T ⊓ Subgroup.centralizer (V₀ : Set G) := by
    refine le_antisymm (le_inf (pCoreOf_two_le_of_isSylowTwoOf hTsyl) hO2V₀) ?_
    exact (inf_le_inf_left T (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVV₀))).trans
      hkey
  have h318 : Hyp318 T M Mp V₀ :=
    { inM := ⟨h.maxTwoLocal, h.T_le⟩
      nonempty := ⟨H, hH⟩
      perfect := h.oTwoUpper_conjClosure.symm
      le_M := h.conjClosure_le
      normal := h.le_normalizer_conjClosure h37 h38 h39
      unique := isUniqueM_mono (h.isUniqueM_sup h37 h38 h39).1
        (sup_le_sup_right (le_conjClosure L T) T) (_root_.sup_le h.conjClosure_le h.T_le)
      reduced := hred
      centralizer := hcent }
  rcases theorem318_three hC58 h317 h.simple h.nonabelian h.qtke h.sylow h318 with
    ⟨hJ, -⟩ | ⟨-, hZ, -⟩
  ·
    exfalso
    obtain ⟨hc, hnot⟩ := hFF
    obtain ⟨A, hA, hAV⟩ :
        ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
      by_contra hcon
      apply hJ
      refine iSup₂_le fun A hA => ?_
      have hAV : A ≤ Subgroup.centralizer (V : Set G) := by
        by_contra hAV
        exact hcon ⟨A, hA, hAV⟩
      rw [← hcent]
      exact (le_inf hA.1 hAV).trans hkey
    have hVel : IsElemAbelian 2 V := isElemAbelian_two_of_le hVV₀ hred.2.2.1
    have hVT : V ≤ T := hVV₀.trans ((le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1
      (isPGroup_two_of_isElemAbelian hred.2.2.1)).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl))
    have hVN : Mp ⊔ T ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
      mem_normalizer_commutator (hred.2.1 hx) (hMpMp hx)
    exact hnot (isFFModule_autOn hVel hVT hVN (hA.1.trans le_sup_right) hA hAV)
  ·
    exact Subgroup.le_centralizer_iff.mp ((hZ H hH).trans inf_le_right)

end CFSG.Quasithin.H13.Ch4
