module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22t_frattini_sup {q : ℕ} [Fact q.Prime] {H K S : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) (hS : CFSG.ABGLocalTools.IsSylowOf q S K) :
    H ≤ K ⊔ (H ⊓ normalizer (S : Set G)) := by
  classical
  haveI : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  obtain ⟨hSK, hSp, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSH : S ≤ H := hSK.trans hKH
  have hS' : CFSG.ABGLocalTools.IsSylowOf q (S.subgroupOf H) (K.subgroupOf H) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨fun x hx => hSK hx, hSp.comap_subtype, ?_⟩
    rwa [Subgroup.relIndex_subgroupOf hKH]
  obtain ⟨S₀, hS₀⟩ := hS'
  have hF : Subgroup.normalizer (((S₀ : Subgroup ↥(K.subgroupOf H)).map
      (K.subgroupOf H).subtype : Subgroup ↥H) : Set ↥H) ⊔ K.subgroupOf H = ⊤ :=
    Sylow.normalizer_sup_eq_top S₀
  rw [hS₀] at hF
  intro h hh
  have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔
      K.subgroupOf H := by
    rw [hF]
    trivial
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hnG : (n : G) ∈ normalizer (S : Set G) := by
    have hn' := hn
    rw [Subgroup.mem_normalizer_iff] at hn' ⊢
    intro x
    constructor
    · intro hx
      exact (hn' ⟨x, hSH hx⟩).1 hx
    · intro hx
      have hxH : x ∈ H := by
        have h1 : (n : G) * x * (n : G)⁻¹ ∈ H := hSH hx
        have := H.mul_mem (H.mul_mem (H.inv_mem n.2) h1) n.2
        simpa [mul_assoc] using this
      exact (hn' ⟨x, hxH⟩).2 hx
  have hh' : h = (n : G) * (k : G) := congrArg Subtype.val hnk.symm
  rw [hh']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨n.2, hnG⟩) (Subgroup.mem_sup_left hk)

theorem uc22p22t_M_le_normalizer_jOf (D : Data G) :
    D.M ≤ normalizer ((proofN D : Subgroup G) : Set G) := by
  have key : ∀ y ∈ D.M, ∀ x ∈ proofN D, y * x * y⁻¹ ∈ proofN D := by
    intro y hy
    refine uc22p22e_conj_jOf (T := D.M) (fun x hx => ?_)
    exact D.M.mul_mem (D.M.mul_mem hy (uc22p22e_jOf_le_self D.M hx)) (D.M.inv_mem hy)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ (D.M.inv_mem hy) _ hx
  simpa [mul_assoc] using this

theorem uc22p22t_exists_sylow_normalizing_jOf (D : Data G) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ Nat.card (proofN D)) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P D.M ∧
      ∀ y ∈ P, ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNM : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  have hMN := uc22p22t_M_le_normalizer_jOf D
  have hTN : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ proofN D) (proofN D) :=
    D.sylowM.inf_of_le_normalizer hNM hMN
  have hFr := uc22p22t_frattini_sup hNM hMN hTN
  set Hn : Subgroup G := D.M ⊓ normalizer ((D.T ⊓ proofN D : Subgroup G) : Set G) with hHn
  have hHnM : Hn ≤ D.M := inf_le_left
  have hMeq : proofN D ⊔ Hn = D.M := le_antisymm (sup_le hNM hHnM) hFr
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p Hn
  refine ⟨P, ?_, ?_⟩
  · have hHnN : Hn ≤ normalizer ((proofN D : Subgroup G) : Set G) := hHnM.trans hMN
    have hprod := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hHnN
    rw [sup_comm, hMeq] at hprod
    have hN0 : (Nat.card (proofN D)).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpN
    have hI0 : (Nat.card ↥(Hn ⊓ proofN D)).factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun hd => hpN (hd.trans ?_)
      exact Subgroup.card_dvd_of_le inf_le_right
    have hfac := congrArg (fun n => n.factorization p) hprod
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hfac
    simp only [Finsupp.add_apply, hN0, hI0, add_zero] at hfac
    refine CFSG.ABGLocalTools.isSylowOf_of_card (hP.le.trans hHnM) ?_
    rw [hP.card_eq, hfac]
  · intro y hy x hx
    have hyN : y ∈ normalizer ((D.T ⊓ proofN D : Subgroup G) : Set G) := (hP.le hy).2
    refine uc22p22e_conj_jOf (T := D.T) (fun x hx => ?_) x hx
    have hxTN : x ∈ D.T ⊓ proofN D :=
      ⟨uc22p22e_jOf_le_self D.T hx, uc22p22e_jOf_le D.sylowM hx⟩
    exact ((Subgroup.mem_normalizer_iff.1 hyN x).1 hxTN).1

theorem uc22p22t_faithful_bar (D : Data G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : G}
    (hcM : c ∈ D.M) (hcp : IsPGroup p (Subgroup.zpowers c))
    (hcomm : ∀ x ∈ jOf D.T, x * c * x⁻¹ * c⁻¹ ∈ centralizer (D.U : Set G))
    (hfixE : ∀ z ∈ proofE D, z ∈ D.U → c * z = z * c) : c ∈ centralizer (D.U : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  obtain ⟨hU1, hUel⟩ := uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
  have hUO : D.U ≤ pCoreOf 2 D.M := hU1.trans inf_le_left
  have hU2 : IsPGroup 2 ↥D.U := uc22p22e_isPGroup_of_elem hUel
  let φ := uc22br4_conjAut D.M D.U hV
  let B : Subgroup ↥D.M := (jOf D.T).subgroupOf D.M
  have hB : IsPGroup 2 ↥B :=
    ((D.sylowM.isPGroup).to_le (uc22p22e_jOf_le_self D.T)).comap_subtype
  let cM : ↥D.M := ⟨c, hcM⟩
  have hord : Odd (orderOf cM) := by
    obtain ⟨k, hk⟩ := hcp ⟨c, Subgroup.mem_zpowers c⟩
    have h1 : c ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    have h4 : Odd (orderOf c) := h3.of_dvd_nat h2
    have h5 : orderOf cM = orderOf c := (Subgroup.orderOf_coe cM).symm
    rwa [h5]
  have hcB : ∀ b ∈ B, φ cM * φ b = φ b * φ cM := by
    intro b hb
    have hbJ : (b : G) ∈ jOf D.T := hb
    have hd := hcomm (b : G) hbJ
    ext v
    show c * ((b : G) * v * (b : G)⁻¹) * c⁻¹ = (b : G) * (c * v * c⁻¹) * (b : G)⁻¹
    set x : G := (b : G) with hx
    have hu : c * (x * (v : G) * x⁻¹) * c⁻¹ ∈ D.U := by
      have := uc22br_gt_conj_mem hV hcM (uc22br_gt_conj_mem hV b.2 v.2)
      simpa [mul_assoc] using this
    have hcen := Subgroup.mem_centralizer_iff.1 hd _ hu
    calc c * (x * (v : G) * x⁻¹) * c⁻¹
        = ((c * (x * (v : G) * x⁻¹) * c⁻¹) * (x * c * x⁻¹ * c⁻¹)) * (x * c * x⁻¹ * c⁻¹)⁻¹ := by
          group
      _ = ((x * c * x⁻¹ * c⁻¹) * (c * (x * (v : G) * x⁻¹) * c⁻¹)) * (x * c * x⁻¹ * c⁻¹)⁻¹ := by
          rw [hcen]
      _ = x * (c * v * c⁻¹) * x⁻¹ := by group
  have hfix : ∀ r : ↥D.U, (∀ b ∈ B, φ b r = r) → φ cM r = r := by
    intro r hr
    have hrT : (r : G) ∈ D.T := uc22p22e_pCoreOf_le_T D (hUO r.2)
    have hrc : ∀ j ∈ jOf D.T, j * (r : G) = (r : G) * j := by
      intro j hj
      have h1 := congrArg Subtype.val
        (hr ⟨j, D.sylowM.le (uc22p22e_jOf_le_self D.T hj)⟩ hj)
      have h2 : j * (r : G) * j⁻¹ = r := h1
      calc j * (r : G) = j * (r : G) * j⁻¹ * j := by group
        _ = (r : G) * j := by rw [h2]
    have hrE : (r : G) ∈ proofE D :=
      uc22p22e_mem_omegaZJ'.2 ⟨hrT, hrc, hUel.2 (r : G) r.2⟩
    have h3 := hfixE (r : G) hrE r.2
    apply Subtype.ext
    show c * (r : G) * c⁻¹ = r
    calc c * (r : G) * c⁻¹ = (r : G) * c * c⁻¹ := by rw [h3]
      _ = r := by group
  have h1 := uc22p22e_thompson φ hU2 hB hord hcB hfix
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h2 : c * v * c⁻¹ = v :=
    congrArg (fun f : MulAut ↥D.U => ((f ⟨v, hv⟩ : ↥D.U) : G)) h1
  calc v * c = c * v * c⁻¹ * c := by rw [h2]
    _ = c * v := by group

theorem uc22p22t_frattini_core {H : Type*} [Group H] [Finite H] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] {K S P : Subgroup H} [K.Normal] (hS : CFSG.ABGLocalTools.IsSylowOf q S K)
    (hP : IsPGroup p P) :
    ∃ X : Subgroup H, IsPGroup p X ∧ X ≤ Subgroup.normalizer (S : Set H) ∧
      (IsCyclic ↥X → IsCyclic ↥(P.map (QuotientGroup.mk' K))) := by
  classical
  obtain ⟨S₀, rfl⟩ := hS
  set N : Subgroup H := Subgroup.normalizer ((S₀.map K.subtype : Subgroup H) : Set H) with hN
  have hF : N ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top S₀
  set π : H →* H ⧸ K := QuotientGroup.mk' K with hπ
  set Q : Subgroup (H ⧸ K) := P.map π with hQ
  set W : Subgroup H := N ⊓ Q.comap π with hW
  have hπW : W.map π = Q := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ N ⊔ K := hF ▸ Subgroup.mem_top y
      obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy'
      have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      have hπ1 : π (n * k) = π n := by
        rw [map_mul, hk1, mul_one]
      refine ⟨n, ⟨hn, ?_⟩, hπ1.symm⟩
      show π n ∈ Q
      rw [← hπ1]
      exact Subgroup.mem_map_of_mem _ hy
  obtain ⟨X₀⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥W))
  set X : Subgroup H := (X₀ : Subgroup ↥W).map W.subtype with hX
  have hXW : X ≤ W := Subgroup.map_subtype_le _
  have hQp : IsPGroup p ↥Q := hP.map π
  have hWQ : ∀ w : ↥W, π (w : H) ∈ Q := fun w => w.2.2
  let f : ↥W →* ↥Q := (π.comp W.subtype).codRestrict Q hWQ
  have hf : Function.Surjective f := by
    rintro ⟨q', hq'⟩
    rw [← hπW] at hq'
    obtain ⟨w, hw, hwq⟩ := hq'
    exact ⟨⟨w, hw⟩, Subtype.ext hwq⟩
  have htop : ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) = ⊤ := by
    symm
    exact (X₀.mapSurjective hf).is_maximal' (hQp.of_equiv Subgroup.topEquiv.symm) le_top
  have hsurj : ∀ q' ∈ Q, ∃ x ∈ X, π x = q' := by
    intro q' hq'
    have h1 : (⟨q', hq'⟩ : ↥Q) ∈ ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) := by
      rw [htop]; trivial
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨x, hx, hxq⟩ := h1
    exact ⟨(x : H), ⟨x, hx, rfl⟩, congrArg Subtype.val hxq⟩
  refine ⟨X, X₀.isPGroup'.map W.subtype, fun x hx => (hXW hx).1, ?_⟩
  intro hXc
  let g : ↥X →* ↥Q := (π.comp X.subtype).codRestrict Q (fun x => (hXW x.2).2)
  have hg : Function.Surjective g := by
    rintro ⟨q', hq'⟩
    obtain ⟨x, hx, hxq⟩ := hsurj q' hq'
    exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
  exact isCyclic_of_surjective g hg

theorem uc22p22t_frattini_core_sub {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {H₀ K S P : Subgroup G} [(K.subgroupOf H₀).Normal] (hKH : K ≤ H₀)
    (hS : CFSG.ABGLocalTools.IsSylowOf q S K) (hP : IsPGroup p P) (hPH : P ≤ H₀) :
    ∃ X : Subgroup G, X ≤ H₀ ∧ IsPGroup p X ∧ X ≤ normalizer (S : Set G) ∧
      (IsCyclic ↥X →
        IsCyclic ↥((P.subgroupOf H₀).map (QuotientGroup.mk' (K.subgroupOf H₀)))) := by
  obtain ⟨hSK, hSp, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSH : S ≤ H₀ := hSK.trans hKH
  have hS' : CFSG.ABGLocalTools.IsSylowOf q (S.subgroupOf H₀) (K.subgroupOf H₀) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨fun x hx => hSK hx, hSp.comap_subtype, ?_⟩
    rwa [Subgroup.relIndex_subgroupOf hKH]
  have hP' : IsPGroup p (P.subgroupOf H₀) := hP.comap_subtype
  obtain ⟨X', hX'p, hX'N, hX'c⟩ := uc22p22t_frattini_core hS' hP'
  refine ⟨X'.map H₀.subtype, Subgroup.map_subtype_le _, hX'p.map _, ?_, ?_⟩
  · rintro _ ⟨x', hx', rfl⟩
    have hx'N := hX'N hx'
    rw [Subgroup.mem_normalizer_iff] at hx'N ⊢
    intro h
    constructor
    · intro hh
      exact (hx'N ⟨h, hSH hh⟩).1 hh
    · intro hh
      have hhH : h ∈ H₀ := by
        have h1 : (x' : G) * h * (x' : G)⁻¹ ∈ H₀ := hSH hh
        have := H₀.mul_mem (H₀.mul_mem (H₀.inv_mem x'.2) h1) x'.2
        simpa [mul_assoc] using this
      exact (hx'N ⟨h, hhH⟩).2 hh
  · intro hc
    apply hX'c
    exact isCyclic_of_injective
      (Subgroup.equivMapOfInjective X' H₀.subtype H₀.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective X' H₀.subtype H₀.subtype_injective).injective

theorem uc22p22t_frattini_bar (D : Data G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {H₀ K S P : Subgroup G} (hKH : K ≤ H₀) (hHK : H₀ ≤ normalizer (K : Set G))
    (hH₀M : H₀ ≤ D.M) (hS : CFSG.ABGLocalTools.IsSylowOf q S K) (hP : IsPGroup p P)
    (hPH : P ≤ H₀) (hPK : P ⊓ K ≤ centralizer (D.U : Set G))
    (hnc : ¬ IsCyclic ↥(mbarImage D.M D.U P)) :
    ∃ X : Subgroup G, X ≤ H₀ ∧ IsPGroup p X ∧ ¬ IsCyclic X ∧ X ≤ normalizer (S : Set G) := by
  classical
  have hV : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  haveI : (K.subgroupOf H₀).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  obtain ⟨X, hXH, hXp, hXN, hXc⟩ := uc22p22t_frattini_core_sub hKH hS hP hPH
  refine ⟨X, hXH, hXp, fun hc => hnc ?_, hXN⟩
  have hQ := hXc hc
  set Q : Subgroup (↥H₀ ⧸ K.subgroupOf H₀) :=
    (P.subgroupOf H₀).map (QuotientGroup.mk' (K.subgroupOf H₀)) with hQdef
  have hPM : P ≤ D.M := hPH.trans hH₀M
  let h : ↥P →* ↥Q :=
    ((QuotientGroup.mk' (K.subgroupOf H₀)).comp (Subgroup.inclusion hPH)).codRestrict Q
      (fun a => ⟨Subgroup.inclusion hPH a, a.2, rfl⟩)
  have hsurj : Function.Surjective h := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨(a : G), ha⟩, rfl⟩
  have hker : h.ker ≤ (uc22br4_phi D.M D.U P hPM).ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    have h1 : QuotientGroup.mk' (K.subgroupOf H₀) (Subgroup.inclusion hPH a) = 1 :=
      congrArg Subtype.val ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (a : G) ∈ P ⊓ K := ⟨a.2, h1⟩
    rw [uc22br4_phi_apply, uc22br_gt_mk_eq_one_iff hV]
    exact hPK h2
  let ψ : ↥Q →* MBar D.M D.U :=
    MonoidHom.liftOfRightInverse h (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨uc22br4_phi D.M D.U P hPM, hker⟩
  have hψ : ψ.comp h = uc22br4_phi D.M D.U P hPM :=
    MonoidHom.liftOfRightInverse_comp h (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨uc22br4_phi D.M D.U P hPM, hker⟩
  have hrange : ψ.range = mbarImage D.M D.U P := by
    rw [← uc22br4_range_phi D.M D.U P hPM, ← hψ, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective h hsurj, Subgroup.map_top]
  haveI : IsCyclic ↥Q := hQ
  have hcyc : IsCyclic ↥ψ.range := isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  rwa [hrange] at hcyc

@[expose] def NatPFact (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ p ∈ D.sig, p ∉ piSet (proofN D) →
    ∀ x ∈ D.M, IsPGroup p (Subgroup.zpowers x) →
      (∀ y ∈ jOf D.T, x * y * x⁻¹ ∈ jOf D.T) → (∀ z ∈ proofE D, x * z * x⁻¹ = z) →
      ∀ y ∈ jOf D.T, x * y * x⁻¹ * y⁻¹ ∈ centralizer (D.U : Set G)

theorem uc22p22t_isSylowOf_mbarImage (D : Data G) {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P D.M) :
    CFSG.ABGLocalTools.IsSylowOf p (mbarImage D.M D.U P) ⊤ := by
  obtain ⟨hPM, hPp, hPidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, ?_, ?_⟩
  · have h1 : IsPGroup p (P.subgroupOf D.M) := hPp.comap_subtype
    exact h1.map (QuotientGroup.mk' (kerAct D.M D.U).normalCore)
  · rw [Subgroup.relIndex_top_right]
    have hdvd : (mbarImage D.M D.U P).index ∣ (P.subgroupOf D.M).index :=
      Subgroup.index_map_dvd (P.subgroupOf D.M) (QuotientGroup.mk'_surjective _)
    intro hd
    exact hPidx (hd.trans hdvd)

theorem uc22p22t_s22_5_2_of (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h31 : S22_3_1 D Ch) (hB : NatPFact D Ch) : S22_5_2 D Ch := by
  classical
  intro h1930 c p hp
  by_contra hpN
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpN' : ¬ p ∣ Nat.card (proofN D) := fun hd => hpN ⟨hpP, hd⟩
  obtain ⟨P, hPsyl, hnJ⟩ := uc22p22t_exists_sylow_normalizing_jOf D hpP hpN'
  have hPM : P ≤ D.M := hPsyl.le
  have hPp : IsPGroup p P := hPsyl.isPGroup
  have hPE : ∀ y ∈ P, ∀ z ∈ proofE D, y * z * y⁻¹ ∈ proofE D := fun y hy =>
    uc22p22e_conj_omegaZJ (hnJ y hy) (fun x hx => by simpa using hnJ y⁻¹ (P.inv_mem hy) x hx)
  have hTE : ∀ y ∈ D.T, ∀ z ∈ proofE D, y * z * y⁻¹ ∈ proofE D := fun y hy =>
    uc22p22e_conj_omegaZJ (uc22p22e_normalizes_jOf_T D y hy)
      (fun x hx => by simpa using uc22p22e_normalizes_jOf_T D y⁻¹ (D.T.inv_mem hy) x hx)
  have hnormE : ∀ {Y : Subgroup G}, (∀ y ∈ Y, ∀ z ∈ proofE D, y * z * y⁻¹ ∈ proofE D) →
      Y ≤ normalizer (proofE D : Set G) := by
    intro Y hY y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hY y hy z hz
    · intro hz
      have := hY y⁻¹ (Y.inv_mem hy) _ hz
      simpa [mul_assoc] using this
  set H₀ : Subgroup G := D.M ⊓ normalizer (proofE D : Set G) with hH₀
  set K : Subgroup G := D.M ⊓ centralizer (proofE D : Set G) with hK
  have hKH : K ≤ H₀ := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hconj : ∀ h ∈ H₀, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    obtain ⟨hhM, hhN⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hkM, hkC⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨D.M.mul_mem (D.M.mul_mem hhM hkM) (D.M.inv_mem hhM), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hN' := (Subgroup.mem_normalizer_iff.1 (inv_mem hhN)) e
    have he' : h⁻¹ * e * h ∈ proofE D := by
      have := hN'.1 he
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hkC _ he'
    calc e * (h * k * h⁻¹) = h * ((h⁻¹ * e * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * e * h)) * h⁻¹ := by rw [h1]
      _ = h * k * h⁻¹ * e := by group
  have hHK : H₀ ≤ normalizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hconj h hh k hk
    · intro hk
      have := hconj h⁻¹ (H₀.inv_mem hh) _ hk
      simpa [mul_assoc] using this
  have hTH : D.T ≤ H₀ := fun y hy => ⟨D.sylowM.le hy, hnormE hTE hy⟩
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H₀ := D.sylowM.of_le hTH inf_le_left
  have hSK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K := hSylH.inf_of_le_normalizer hKH hHK
  have hSeq : D.T ⊓ K = proofS D := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxT, (Subgroup.mem_inf.1 hxK).2⟩
    · intro hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxT, Subgroup.mem_inf.2 ⟨D.sylowM.le hxT, hxC⟩⟩
  have hPH : P ≤ H₀ := fun y hy => ⟨hPM hy, hnormE hPE hy⟩
  have hPK : P ⊓ K ≤ centralizer (D.U : Set G) := by
    intro x hx
    obtain ⟨hxP, hxK⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨_, hxC⟩ := Subgroup.mem_inf.1 hxK
    have hxM : x ∈ D.M := hPM hxP
    have hxp : IsPGroup p (Subgroup.zpowers x) := hPp.to_le (Subgroup.zpowers_le.2 hxP)
    have hxE : ∀ z ∈ proofE D, x * z * x⁻¹ = z := fun z hz => by
      have h1 := Subgroup.mem_centralizer_iff.1 hxC z hz
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [h1]
        _ = z := by group
    have hcomm := hB h1930 c p hp hpN x hxM hxp (hnJ x hxP) hxE
    refine uc22p22t_faithful_bar D hpP hp2 hxM hxp (fun y hy => ?_)
      (fun z hz _ => (Subgroup.mem_centralizer_iff.1 hxC z hz).symm)
    have h2 := (centralizer (D.U : Set G)).inv_mem (hcomm y hy)
    have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  have hrk : 1 < CFSG.pRank p (MBar D.M D.U) :=
    uc22p22n_one_lt_pRank_mbar D hx h61 (uc22p22e_inCalV_U D) c.hU p hp
  have hnc : ¬ IsCyclic ↥(mbarImage D.M D.U P) := by
    refine uc22p22e_not_isCyclic_sylow hpP (uc22p22t_isSylowOf_mbarImage D hPsyl) ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  obtain ⟨X, hXH, hXp, hXnc, hXN⟩ :=
    uc22p22t_frattini_bar D hKH hHK inf_le_left (hSeq ▸ hSK) hPp hPH hPK hnc
  exact (h31 h1930 c).2 (uc22p22e_calCGS_le D h61 hp (hXH.trans inf_le_left) hXp hXnc hXN
    (inf_le_left : proofS D ≤ D.T))

end CFSG.LocalAnalysis.UniquenessCase.UC22
