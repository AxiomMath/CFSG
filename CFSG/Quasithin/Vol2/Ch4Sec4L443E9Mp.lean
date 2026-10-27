module

public import CFSG.Quasithin.Vol2.Ch4Sec4W446

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.A4
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem commutator_inf_centralizer_le (s : Setting443 G T M L B Tp VB) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) :
    ⁅conjClosure L T ⊓ Subgroup.centralizer (VB : Set G), conjClosure L T⁆ ≤
      pCoreOf 2 (conjClosure L T) := by
  set Mp := conjClosure L T with hMp
  set Q := pCoreOf 2 Mp with hQ
  have h := s.hyp421
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_normalizer_of_hyp421 h h37 h39
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := le_normalizer_conjClosure L T
  have hMpMp : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hTMp
  have hQN : Mp ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    hMpMp.trans (normalizer_le_normalizer_pCoreOf 2 Mp)
  have hVN : Mp ⊔ T ≤ Subgroup.normalizer (VB : Set G) := s.hyp.VB_normalized
  have hCN : Mp ⊔ T ≤ Subgroup.normalizer (Subgroup.centralizer (VB : Set G) : Set G) :=
    fun x hx => mem_normalizer_centralizer_of_mem_normalizer (hVN hx)
  have hVL : ¬ L ≤ Subgroup.centralizer (VB : Set G) := by
    intro hLC
    have hMpC : Mp ≤ Subgroup.centralizer (VB : Set G) := conjClosure_le fun t ht l hl =>
      (Subgroup.mem_normalizer_iff.mp (hCN (Subgroup.mem_sup_right ht)) l).mp (hLC hl)
    apply s.hyp.VB_ne_bot
    rw [s.hyp.VB_eq]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hMpC)
  set N := Mp ⊓ Subgroup.centralizer (VB : Set G) with hN
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
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLMp)
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
  rw [Subgroup.commutator_le]
  intro n hn m hm
  exact (hMpX hm).2.2.2 n hn

omit [Finite G] in
theorem LB_le (L T B : Subgroup G) :
    perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤ conjClosure L T :=
  (perfectCore_le _).trans inf_le_left

theorem commutator_le_pCoreOf_LB (s : Setting443 G T M L B Tp VB) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) {N : Subgroup G}
    (hNL : N ≤ perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))
    (hNV : N ≤ Subgroup.centralizer (VB : Set G)) :
    ⁅N, perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))⁆ ≤
      pCoreOf 2 (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  have hLBMp := LB_le L T B
  have h1 : ⁅N, LB⁆ ≤ LB := commutator_le_right_of_le_normalizer (hNL.trans Subgroup.le_normalizer)
  have h2 : ⁅N, LB⁆ ≤ pCoreOf 2 (conjClosure L T) :=
    (Subgroup.commutator_mono (le_inf (hNL.trans hLBMp) hNV) hLBMp).trans
      (commutator_inf_centralizer_le s h37 h39)
  have hN : LB ≤ Subgroup.normalizer ((LB ⊓ pCoreOf 2 (conjClosure L T) : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx)
      (le_normalizer_pCoreOf 2 _ (hLBMp hx))
  exact (le_inf h1 h2).trans (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN
    ((pCoreOf_isPGroup 2 _).to_le inf_le_right))

theorem MB_le_normalizer_LB (s : Setting443 G T M L B Tp VB) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    M ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer
      (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) : Set G) := fun _ hx =>
  normalizer_le_normalizer_perfectCore _ (mem_normalizer_inf
    (s.hyp421.le_normalizer_conjClosure h37 h38 h39 hx.1)
    (mem_normalizer_centralizer_of_mem_normalizer hx.2))

theorem pCoreOf_LB_le (s : Setting443 G T M L B Tp VB) :
    pCoreOf 2 (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ≤
      pCoreOf 2 (conjClosure L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  set X := pCoreOf 2 LB with hX
  set Q := pCoreOf 2 (conjClosure L T) with hQ
  have hLBMp := LB_le L T B
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    ((pCoreOf_le 2 LB).trans hLBMp).trans (le_normalizer_pCoreOf 2 _)
  have hY2 : IsPGroup 2 ↥(X ⊔ Q) :=
    IsPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 LB) (pCoreOf_isPGroup 2 _) hXQ
  have hYQ : X ⊔ Q ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hXQ ((pCoreOf_le 2 _).trans (le_normalizer_pCoreOf 2 _))
  have hQY : Q ≤ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((commutator_le_right_of_le_normalizer hYQ).trans le_sup_right)
  have hLBY : LB ≤ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G) := fun x hx => by
    have h1 : x ∈ Subgroup.normalizer (X : Set G) := le_normalizer_pCoreOf 2 LB hx
    have h2 : x ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 _ (hLBMp hx)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have hMpY : conjClosure L T ≤ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G) := by
    rw [lemma_4_4_5_orbit s.hyp.toHyp4_4_1TwoOrbit]
    exact sup_le hLBY hQY
  have hYle : X ⊔ Q ≤ conjClosure L T :=
    sup_le ((pCoreOf_le 2 LB).trans hLBMp) (pCoreOf_le 2 _)
  exact le_sup_left.trans (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYle hMpY hY2)

theorem VB_le_centralizer_pCoreOf_LB (s : Setting443 G T M L B Tp VB) :
    VB ≤ Subgroup.centralizer
      (pCoreOf 2 (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCoreOf 2 (conjClosure L T) ≤ pCoreOf 2 (conjClosure L T ⊔ T) := by
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      ?_ (pCoreOf_isPGroup 2 _)
    exact sup_le (le_normalizer_pCoreOf 2 _)
      ((le_normalizer_conjClosure L T).trans (normalizer_le_normalizer_pCoreOf 2 _))
  exact fun v hv => Subgroup.centralizer_le ((pCoreOf_LB_le s).trans hO2)
    (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).2.1

end CFSG.Quasithin.H13.Ch4.E443
