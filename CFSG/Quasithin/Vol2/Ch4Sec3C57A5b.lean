module

public import CFSG.Quasithin.Vol2.Ch4Sec3C57A5a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCFin
public import CFSG.Quasithin.H13.VolIC113

public section

namespace CFSG.Quasithin.H13.Ch4.C57

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G] {H M₀ R K : Subgroup G}

theorem card_conj_inf (U : Subgroup G) (y : G) :
    Nat.card ↥(conjSubgroup U y ⊓ Subgroup.centralizer (U : Set G)) =
      Nat.card ↥(U ⊓ Subgroup.centralizer (conjSubgroup U y⁻¹ : Set G)) := by
  have h1 : conjSubgroup (U ⊓ Subgroup.centralizer (conjSubgroup U y⁻¹ : Set G)) y =
      conjSubgroup U y ⊓ Subgroup.centralizer (U : Set G) := by
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_inv_conjSubgroup]
  rw [← h1, C5.card_conjSubgroup]

namespace Setup

variable (h : Setup H M₀ R K)
include h

omit [Finite G] in
theorem R_le_normalizer_conj {y : G} (hy : y ∈ M₀) :
    R ≤ Subgroup.normalizer (conjSubgroup (blockU K) y : Set G) :=
  C5.le_normalizer_conj (h.normal_R hy) fun _ hr =>
    C1.mem_normalizer_blockU (h.R_le_normalizer_K hr)

omit [Finite G] in
theorem conj_elem (y : G) : IsElemAbelian 2 (conjSubgroup (blockU K) y) :=
  C5.isElemAbelian_two_iff.mpr ((C1.elemAb2_blockU h.short).conjSubgroup y)

theorem im_conj_eq (P : A5Pi K) (hR : P.im R = Dstd) {y : G} (hy : y ∈ M₀)
    (hy1 : ¬ conjSubgroup (blockU K) y ≤ pCoreOf 2 H) :
    P.im (conjSubgroup (blockU K) y) = Estd := by
  classical
  set U := blockU K with hU
  have hy' : y⁻¹ ∈ M₀ := inv_mem hy
  have hVR : conjSubgroup U y ≤ R := h.conj_le_R hy
  have hV'R : conjSubgroup U y⁻¹ ≤ R := h.conj_le_R hy'
  have hVN := hVR.trans h.R_le_normalizer_K
  have hV'N := hV'R.trans h.R_le_normalizer_K
  have hXD : P.im (conjSubgroup U y) ≤ Dstd := hR ▸ P.im_mono hVR
  have hYD : P.im (conjSubgroup U y⁻¹) ≤ Dstd := hR ▸ P.im_mono hV'R
  obtain ⟨hXsq, hXc⟩ := P.im_elemAbelian (h.conj_elem y)
  obtain ⟨hYsq, hYc⟩ := P.im_elemAbelian (h.conj_elem y⁻¹)
  obtain ⟨a, haX, b, hbX, habX, hcX, hfX⟩ := exists_four_card _ hXsq hXc
  obtain ⟨c, hcY, d, hdY, -, hcY', hfY⟩ := exists_four_card _ hYsq hYc
  have h16 : ∀ z : G, Nat.card ↥(conjSubgroup U z) = 16 := fun z => by
    rw [C5.card_conjSubgroup, P.card_blockU]
  have e1 := P.card_im_mul hVN
  have e2 := P.card_im_mul hV'N
  have f1 := P.card_fix hVN
  have f2 := P.card_fix hV'N
  have s1 := card_conj_inf U y
  have s2 := card_conj_inf U y⁻¹
  rw [inv_inv] at s2
  have k1 : (four a b).card * (fixOf c d).card = 16 := by
    rw [← hcX, ← hfY, ← f2, ← s1, e1, h16]
  have k2 : (four c d).card * (fixOf a b).card = 16 := by
    rw [← hcY', ← hfX, ← f1, ← s2, e2, h16]
  have hne : four a b ≠ {1} := by
    intro heq
    apply hy1
    intro v hv
    have hπ : P.π ⟨v, hVN hv⟩ = 1 := by
      have hm := P.pi_mem_im (K := conjSubgroup U y) (y := ⟨v, hVN hv⟩) hv
      rw [habX, heq, Finset.mem_singleton] at hm
      exact hm
    have hc := (P.hker _).1 hπ
    rw [← h.R_inf_centralizer_eq]
    refine ⟨hVR hv, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have := hc u hu
    calc u * v = (v * u * v⁻¹) * v := by rw [this]
      _ = v * u := by group
  have hnorm : ∀ σ ∈ Dset, ∀ g ∈ four a b, σ * g * σ⁻¹ ∈ four a b := by
    intro σ hσ g hg
    rw [← habX] at hg ⊢
    have hσ' : σ ∈ P.im R := by rw [hR]; exact hσ
    exact im_conj_mem P.toPiData (h.R_le_normalizer_conj hy) σ hσ' g hg
  have hab := fin_pair a ((mem_Dstd a).1 (hXD haX)) b ((mem_Dstd b).1 (hXD hbX))
    ⟨hXsq a haX, hXsq b hbX, hXc a haX b hbX, hne, hnorm⟩ c ((mem_Dstd c).1 (hYD hcY)) d
    ((mem_Dstd d).1 (hYD hdY)) (hYsq c hcY) (hYsq d hdY) (hYc c hcY d hdY) k1 k2
  ext g
  rw [habX g, hab, mem_Estd]

theorem cent_conj (P : A5Pi K) (hR : P.im R = Dstd) {y : G} (hy : y ∈ M₀)
    (hy1 : ¬ conjSubgroup (blockU K) y ≤ pCoreOf 2 H) :
    blockU K ⊓ Subgroup.centralizer (conjSubgroup (blockU K) y : Set G) =
        blockU K ⊓ conjSubgroup (blockU K) y ∧
      blockU K ⊓ conjSubgroup (blockU K) y =
        conjSubgroup (blockU K) y ⊓ Subgroup.centralizer (blockU K : Set G) ∧
      Nat.card ↥(blockU K ⊓ conjSubgroup (blockU K) y) = 4 := by
  set U := blockU K with hU
  set V := conjSubgroup U y with hV
  have hVR : V ≤ R := h.conj_le_R hy
  have hVN : V ≤ Subgroup.normalizer (K : Set G) := hVR.trans h.R_le_normalizer_K
  have him := h.im_conj_eq P hR hy hy1
  have hcard1 : Nat.card ↥(U ⊓ Subgroup.centralizer (V : Set G)) = 4 := by
    rw [P.card_fix hVN, him, card_fix_Estd]
  have hcard2 : Nat.card ↥(V ⊓ Subgroup.centralizer (U : Set G)) = 4 := by
    have e1 : Nat.card (P.im V) * Nat.card ↥(V ⊓ Subgroup.centralizer (U : Set G)) =
        Nat.card V := P.card_im_mul hVN
    have hV16 : Nat.card V = 16 := by rw [hV, C5.card_conjSubgroup, P.card_blockU]
    rw [him, Estd_card, hV16] at e1
    omega
  have h1 : U ⊓ Subgroup.centralizer (V : Set G) ≤ U ⊓ V := by
    intro u hu
    obtain ⟨huU, huC⟩ := hu
    refine ⟨huU, ?_⟩
    set f : evenWeight 5 := Multiplicative.toAdd (P.β ⟨u, huU⟩) with hf
    have hfix : f ∈ FixΔ Estd := by
      rw [← him]
      intro σ hσ
      obtain ⟨z, hz, rfl⟩ := (P.mem_im).1 hσ
      have hc := Subgroup.mem_centralizer_iff.1 huC z hz
      have h' := P.hcomp z ⟨u, huU⟩ ⟨u, huU⟩ (by
        show u = (z : G) * u * (z : G)⁻¹
        rw [hc]; group)
      exact h'.symm
    have hfe : isEven f.1 := (mem_evenWeight_iff f.1).1 f.2
    have hfE : ∀ σ ∈ Eset, pact σ f.1 = f.1 := fun σ hσ =>
      congrArg Subtype.val (hfix σ ((mem_Estd σ).2 hσ))
    obtain ⟨t, htE, w, hwe, hw⟩ := fix_comm f.1 hfe hfE
    have htV : t ∈ P.im V := by rw [him]; exact (mem_Estd t).2 htE
    obtain ⟨v, hvV, hvt⟩ := (P.mem_im).1 htV
    have hw' : w ∈ evenWeight 5 := (mem_evenWeight_iff w).2 hwe
    set u' : ↥(blockU K) := P.β.symm (Multiplicative.ofAdd ⟨w, hw'⟩) with hu'
    have hu'β : Multiplicative.toAdd (P.β u') = ⟨w, hw'⟩ := by simp [hu']
    have hvU' : (v : G) * (u' : G) * (v : G)⁻¹ ∈ blockU K :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := K) v.2) u').mp u'.2
    have hcomp := P.hcomp v u' ⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ rfl
    have heq : (⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ : ↥(blockU K)) * u'⁻¹ = ⟨u, huU⟩ := by
      apply P.β.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hcomp, hvt, hu'β]
      apply Subtype.ext
      funext i
      have hi := congrFun hw i
      simp only [Pi.add_apply] at hi
      show pact t w i + -(w i) = f.1 i
      rw [← hi]
      generalize pact t w i = a
      generalize w i = b
      revert a b
      decide
    have hu : u = (v : G) * (u' : G) * (v : G)⁻¹ * (u' : G)⁻¹ := by
      have := congrArg Subtype.val heq
      simpa using this.symm
    rw [hu]
    have h3 : (u' : G) * (v : G)⁻¹ * (u' : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (h.R_le_normalizer_conj hy (h.blockU_le_R u'.2))
        ((v : G)⁻¹)).1 (inv_mem hvV)
    have := mul_mem hvV h3
    simpa [mul_assoc] using this
  have h2 : U ⊓ V ≤ V ⊓ Subgroup.centralizer (U : Set G) := by
    intro u hu
    exact ⟨hu.2, Subgroup.mem_centralizer_iff.2 fun u' hu' => blockU_comm_blockU h.short hu' hu.1⟩
  have e1 := Subgroup.eq_of_le_of_card_ge h1
    (by rw [hcard1]; exact (Subgroup.card_le_of_le h2).trans hcard2.le)
  have e2 := Subgroup.eq_of_le_of_card_ge h2 (by rw [hcard2, ← e1, hcard1])
  exact ⟨e1, e2, by rw [← e1, hcard1]⟩

theorem comm_conj (h5 : IsAltType K 5) (P : A5Pi K) (hR : P.im R = Dstd) {y : G} (hy : y ∈ M₀)
    (hy1 : ¬ conjSubgroup (blockU K) y ≤ pCoreOf 2 H) {d v : G}
    (hd : d ∈ R ⊓ Subgroup.centralizer (K : Set G)) (hv : v ∈ conjSubgroup (blockU K) y) :
    d * v = v * d := by
  have hVR : conjSubgroup (blockU K) y ≤ R := h.conj_le_R hy
  set c := d * v * d⁻¹ * v⁻¹ with hc
  have hcV : c ∈ conjSubgroup (blockU K) y := by
    have := (Subgroup.mem_normalizer_iff.mp (h.R_le_normalizer_conj hy hd.1) v).mp hv
    exact mul_mem this (inv_mem hv)
  have hDn : v ∈ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :
      Set G) :=
    C5.mem_normalizer_inf (Subgroup.le_normalizer (hVR hv))
      (C5.mem_normalizer_centralizer (h.R_le_normalizer_K (hVR hv)))
  have hcD : c ∈ R ⊓ Subgroup.centralizer (K : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp hDn d⁻¹).mp (inv_mem hd)
    have e : c = d * (v * d⁻¹ * v⁻¹) := by rw [hc]; group
    rw [e]
    exact mul_mem hd this
  have hUK : blockU K ≤ K := (C1.blockU_le_blockQ h.short).trans (C1.blockQ_le K)
  have hcU : c ∈ blockU K := by
    have : c ∈ conjSubgroup (blockU K) y ⊓ Subgroup.centralizer (blockU K : Set G) :=
      ⟨hcV, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hcD.2 u (hUK hu))⟩
    rw [← (h.cent_conj P hR hy hy1).2.1] at this
    exact this.1
  have hcZ : c ∈ blockZ K := ⟨hcU, hcD.2⟩
  rw [blockZ_eq_bot_of_alt5 h.short h5, Subgroup.mem_bot] at hcZ
  have : d * v * d⁻¹ = v := by
    have := congrArg (· * v) hcZ
    simpa [hc, mul_assoc] using this
  calc d * v = (d * v * d⁻¹) * d := by group
    _ = v * d := by rw [this]

theorem pCoreOf_eq_sup (h5 : IsAltType K 5) :
    pCoreOf 2 H = blockU K ⊔ (R ⊓ Subgroup.centralizer (K : Set G)) := by
  have hT : IsSylowTwoOf R (K ⊔ R) := h.H_eq ▸ h.sylow
  have := (VolI.stmtC113c G K R hT h.R_le_normalizer_K h.short h5).1
  rw [h.H_eq]
  exact this

theorem conj_pCoreOf {x : G} (hx : x ∈ M₀) :
    conjSubgroup (pCoreOf 2 H) x =
      R ⊓ Subgroup.centralizer (conjSubgroup (blockU K) x : Set G) := by
  rw [← h.R_inf_centralizer_eq, C5.conjSubgroup_inf, C5.conjSubgroup_centralizer,
    C5.conjSubgroup_eq_self (h.normal_R hx)]

theorem pCoreOf_eq_sup_inf (h5 : IsAltType K 5) (P : A5Pi K) (hR : P.im R = Dstd) {y : G}
    (hy : y ∈ M₀) (hy1 : ¬ conjSubgroup (blockU K) y ≤ pCoreOf 2 H) :
    pCoreOf 2 H = blockU K ⊔ (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) y) := by
  refine le_antisymm ?_ (sup_le h.blockU_le_pCoreOf inf_le_left)
  conv_lhs => rw [h.pCoreOf_eq_sup h5]
  refine sup_le_sup_left (fun d hd => ⟨?_, ?_⟩) _
  · rw [h.pCoreOf_eq_sup h5]; exact Subgroup.mem_sup_right hd
  · rw [h.conj_pCoreOf hy]
    exact ⟨hd.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (h.comm_conj h5 P hR hy hy1 hd hv).symm⟩

theorem sqSub_eq_bot (h5 : IsAltType K 5) (P : A5Pi K) (hR : P.im R = Dstd) {x : G}
    (hx : x ∈ M₀) (hx1 : ¬ conjSubgroup (blockU K) x ≤ pCoreOf 2 H) :
    C5.sqSub (pCoreOf 2 H) = ⊥ := by
  have hx2 := h.conj_inv_not_le hx hx1
  have e1 := h.pCoreOf_eq_sup_inf h5 P hR hx hx1
  have e2 := h.pCoreOf_eq_sup_inf h5 P hR (inv_mem hx) hx2
  set Q := pCoreOf 2 H with hQ
  set U := blockU K with hU
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := C1.blockU_sq h.short
  have e3 : conjSubgroup Q x = conjSubgroup U x ⊔ (conjSubgroup Q x ⊓ Q) := by
    conv_lhs => rw [e2]
    rw [C5.conjSubgroup_sup, C5.conjSubgroup_inf, C5.conjSubgroup_inv_conjSubgroup]
  have s1 : C5.sqSub Q = C5.sqSub (Q ⊓ conjSubgroup Q x) := by
    conv_lhs => rw [e1]
    exact C5.sqSub_sup_eq hU2 fun u hu a ha => (h.pCoreOf_comm ha.1 hu).symm
  have s2 : C5.sqSub (conjSubgroup Q x) = C5.sqSub (conjSubgroup Q x ⊓ Q) := by
    conv_lhs => rw [e3]
    refine C5.sqSub_sup_eq (fun v hv => (C5.isElemAbelian_two_iff.mp (h.conj_elem x)).2 v hv)
      fun v hv a ha => ?_
    have h1 : x * a * x⁻¹ ∈ Q := mem_conjSubgroup_iff.mp ha.1
    have h2 : x * v * x⁻¹ ∈ U := mem_conjSubgroup_iff.mp hv
    have hc := h.pCoreOf_comm h1 h2
    have : x * (v * a) * x⁻¹ = x * (a * v) * x⁻¹ := by
      calc x * (v * a) * x⁻¹ = (x * v * x⁻¹) * (x * a * x⁻¹) := by group
        _ = (x * a * x⁻¹) * (x * v * x⁻¹) := hc.symm
        _ = x * (a * v) * x⁻¹ := by group
    simpa using this
  have hxQ : conjSubgroup (C5.sqSub Q) x = C5.sqSub Q := by
    rw [C5.conjSubgroup_sqSub, s2, inf_comm, ← s1]
  have hHQ : H ≤ Subgroup.normalizer (C5.sqSub Q : Set G) := fun g hg =>
    conjSubgroup_eq_iff_mem_normalizer.mp (C5.conjSubgroup_sqSub_of_mem_normalizer
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H hg))
  exact h.eq_bot hx (h.not_mem_normalizer hx1) (C5.sqSub_le_self.trans h.pCoreOf_le_R)
    (h.K_le.trans hHQ) (h.R_le_H.trans hHQ)
    (fun g hg => conjSubgroup_eq_iff_mem_normalizer.mp
      (C5.conjSubgroup_sqSub_of_mem_normalizer (h.mem_normalizer_pCoreOf hg)))
    (conjSubgroup_eq_iff_mem_normalizer.mp hxQ)

theorem card_le_aU (P : A5Pi K) {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAR : A ≤ R) :
    Nat.card A ≤ Nat.card ↥((A ⊓ Subgroup.centralizer (blockU K : Set G)) ⊔ blockU K) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAR.trans h.R_le_normalizer_K
  set C := A ⊓ Subgroup.centralizer (blockU K : Set G) with hC
  have hcomm : ∀ k ∈ C, ∀ u ∈ blockU K, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(C ⊓ blockU K) ≤
      Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA ha hx.1.1
  have h4 := P.card_im_mul hAN
  have h5 := P.card_fix hAN
  have h6 := P.card_blockU
  have h7 := card_mul_fix_le (P.im A) (P.im_elemAbelian hA).1 (P.im_elemAbelian hA).2
  have hbpos : 0 < Nat.card ↥(C ⊓ blockU K) := Nat.card_pos
  rw [h5] at h3
  set p := Nat.card (P.im A)
  set f := Nat.card (FixΔ (P.im A))
  set b := Nat.card ↥(C ⊓ blockU K)
  set a := Nat.card ↥(C ⊔ blockU K)
  set k := Nat.card ↥C
  rw [← h4]
  have hab : a * b = k * 16 := by rw [h2, h6]
  have h9 : (p * k) * b ≤ a * b := by
    calc (p * k) * b ≤ (p * k) * f := Nat.mul_le_mul_left _ h3
      _ = k * (p * f) := by ring
      _ ≤ k * 16 := Nat.mul_le_mul_left _ h7
      _ = a * b := hab.symm
  exact Nat.le_of_mul_le_mul_right h9 hbpos

theorem isMaxElemAbelian (h5 : IsAltType K 5) (P : A5Pi K) (hR : P.im R = Dstd) {x : G}
    (hx : x ∈ M₀) (hx1 : ¬ conjSubgroup (blockU K) x ≤ pCoreOf 2 H) :
    IsMaxElemAbelian R (pCoreOf 2 H) := by
  have hsq := h.sqSub_eq_bot h5 P hR hx hx1
  have he : IsElemAbelian 2 (pCoreOf 2 H) := C5.isElemAbelian_two_iff.mpr
    ⟨C5.comm_of_sq_eq_one (C5.sqSub_eq_bot_iff.mp hsq), C5.sqSub_eq_bot_iff.mp hsq⟩
  refine ⟨h.pCoreOf_le_R, he, fun A hAR hA => (h.card_le_aU P hA hAR).trans ?_⟩
  refine Subgroup.card_le_of_le (sup_le (fun a ha => ?_) h.blockU_le_pCoreOf)
  rw [← h.R_inf_centralizer_eq]
  exact ⟨hAR ha.1, ha.2⟩

end Setup

end CFSG.Quasithin.H13.Ch4.C57
