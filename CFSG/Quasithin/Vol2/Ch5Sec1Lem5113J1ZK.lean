module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113J1Seven
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Mod
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartan
public import CFSG.Walter.J1Props.Aut

public section

namespace CFSG.Quasithin.H13

section J1

open CFSG.Walter CFSG.Walter.J1Props CFSG.Open CFSG.Blueprint

variable {Q : Type} [Group Q]

theorem exists_eq_conj_of_j1
    (e : Q ≃* NativeSporadic.Carrier .J1) (ξ : MulAut Q) : ∃ g : Q, ξ = MulAut.conj g := by
  let ε : Q ≃* walterJ1 := e.trans walterJ1EquivNative.symm
  obtain ⟨g, hg⟩ := J3_aut (ε.symm.trans (ξ.trans ε))
  refine ⟨ε.symm g, MulEquiv.ext fun x => ε.injective ?_⟩
  have h1 := congrArg (fun f : MulAut walterJ1 => f (ε x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [h1]
  simp

theorem eq_one_of_forall_commute_of_j1
    (e : Q ≃* NativeSporadic.Carrier .J1) {z : Q} (hz : ∀ k : Q, z * k = k * z) : z = 1 := by
  let ε : Q ≃* walterJ1 := e.trans walterJ1EquivNative.symm
  have hc : Subgroup.center walterJ1 = ⊥ :=
    CFSG.Sporadic.Schreier.center_eq_bot_of_simple isSimpleGroup_walterJ1 rels_aut.1
  have hmem : ε z ∈ Subgroup.center walterJ1 := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨k', rfl⟩ := ε.surjective k
    rw [← map_mul, ← map_mul, hz k']
  rw [hc, Subgroup.mem_bot] at hmem
  exact ε.injective (by rw [hmem, map_one])

theorem eq_one_of_commute_of_j1
    (e : Q ≃* NativeSporadic.Carrier .J1) {a b : Q} (ha : Nat.Coprime (orderOf a) 30)
    (hb : orderOf b = 3) (hab : a * b = b * a) : a = 1 := by
  let ε : Q ≃* walterJ1 := e.trans walterJ1EquivNative.symm
  have h1 : ε a = 1 := jankoHyp.eq_one_of_coprime_of_commute (x := ε b) (y := ε a)
    (by rwa [MulEquiv.orderOf_eq]) (Or.inr (Or.inl (by rwa [MulEquiv.orderOf_eq])))
    (by rw [← map_mul, ← map_mul, hab])
  exact ε.injective (by rw [h1, map_one])

end J1

section Odd

theorem eq_one_of_mul_self_of_pow_odd {M : Type*} [Monoid M] {a : M} (h2 : a * a = 1) {r : ℕ}
    (hr : Odd r) (har : a ^ r = 1) : a = 1 := by
  obtain ⟨j, rfl⟩ := hr
  rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul] at har
  exact har

theorem eq_one_of_mem_of_pow_odd {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {d : G} (hd : d ∈ P) {r : ℕ} (hr : Odd r) (hdr : d ^ r = 1) : d = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨d, hd⟩
  have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf d ∣ Nat.gcd (2 ^ k) r :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hdr)
  have h3 : Nat.gcd (2 ^ k) r = 1 := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hr)
  rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact h2

theorem eq_one_of_mem_of_mem_odd {G : Type*} [Group G] [Finite G] {P D : Subgroup G}
    (hP : IsPGroup 2 P) (hD : Odd (Nat.card D)) {d : G} (hdP : d ∈ P) (hdD : d ∈ D) : d = 1 := by
  have h1 : (⟨d, hdD⟩ : ↥D) ^ Nat.card D = 1 := pow_card_eq_one'
  have h2 := congrArg Subtype.val h1
  rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
  exact eq_one_of_mem_of_pow_odd hP hdP hD h2

theorem coprime_seven_two_pow_add_one (m : ℕ) : Nat.Coprime 7 (2 ^ m + 1) := by
  have key : ∀ m : ℕ, 2 ^ m % 7 = 1 ∨ 2 ^ m % 7 = 2 ∨ 2 ^ m % 7 = 4 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      generalize 2 ^ k = t at ih ⊢
      omega
  refine (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr fun h7 => ?_
  have h := key m
  generalize 2 ^ m = t at h h7
  omega

end Odd

section Nat

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem IsNatModCh5.mem_centralizer_of_fix_odd {L W : Subgroup G} {n : ℕ}
    (h : IsNatModCh5 L W n) {d w : G} (hd : d ∈ L) {r : ℕ} (hr : Odd r) (hdr : d ^ r = 1)
    (hw : w ∈ W) (hw1 : w ≠ 1) (hdw : d * w * d⁻¹ = w) :
    d ∈ Subgroup.centralizer (W : Set G) := by
  let D := h.data
  let g : Subgroup.normalizer (W : Set G) := ⟨d, h.1 hd⟩
  obtain ⟨A, hA⟩ := D.exists_matrix_of_mem g hd
  have hv : Multiplicative.toAdd (D.E ⟨w, hw⟩) ≠ 0 := by
    intro h0
    apply hw1
    have h1 : D.E ⟨w, hw⟩ = 1 := toAdd_eq_zero.mp h0
    have h2 : (⟨w, hw⟩ : ↥W) = 1 := (map_eq_one_iff D.E D.E.injective).mp h1
    exact congrArg Subtype.val h2
  have hgw : conjAct W g ⟨w, hw⟩ = ⟨w, hw⟩ :=
    Subtype.ext (by rw [conjAct_apply_coe]; exact hdw)
  have hAv : (A : Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd (D.E ⟨w, hw⟩)) =
      Multiplicative.toAdd (D.E ⟨w, hw⟩) := by
    rw [← hA, ← D.toAdd_E_conj, hgw]
  have hA2 := sl2_mul_self_eq_one_of_fix D.two_eq_zero (A : Matrix (Fin 2) (Fin 2) D.K) A.2 hv hAv
  have hinv : Function.Involutive fun y => (A : Matrix (Fin 2) (Fin 2) D.K).mulVec y := by
    intro y
    simp only [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec]
  have hgr : g ^ r = 1 := Subtype.ext (by simpa [g] using hdr)
  have hconj : ⇑(D.conj g) = fun y => (A : Matrix (Fin 2) (Fin 2) D.K).mulVec y := funext hA
  apply D.mem_centralizer_of_conj_eq g
  intro x
  have h3 := D.conj_eq_of_mem_centralizer (g ^ r) (by rw [hgr]; exact Subgroup.one_mem _) x
  rw [D.conj_pow, hconj, hinv.iterate_odd hr] at h3
  rw [hA]
  exact h3

variable [Finite G]

theorem Hyp5_0_1.conj_ne_of_isNatModCh5_odd {T M L : Subgroup G} {n : ℕ}
    (h : Hyp5_0_1 G T M L n) {W : Subgroup G} {k : ℕ} (hW : IsNatModCh5 L W k) {d w : G}
    (hd : d ∈ L) {r : ℕ} (hr : Odd r) (hdr : d ^ r = 1) (hd1 : d ≠ 1) (hw : w ∈ W)
    (hw1 : w ≠ 1) : d * w * d⁻¹ ≠ w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdw
  have hc := hW.mem_centralizer_of_fix_odd hd hr hdr hw hw1 hdw
  have hWne : ⁅W, L⁆ ≠ ⊥ := by
    rw [hW.commutator_eq]
    intro hb
    rw [hb, Subgroup.mem_bot] at hw
    exact hw1 hw
  have hle := h.inf_centralizer_le hW.1 hWne
  exact hd1 (eq_one_of_mem_of_pow_odd (pCoreOf_isPGroup 2 L) (hle ⟨hd, hc⟩) hr hdr)

theorem QCoord.eq_one_of_fix_odd {L N S : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {ψ : ↥(autOn L N) ≃* SL(2, F)} {Y : ↥N →* Multiplicative (Fin 2 → F)}
    (hc : QCoord L N S F ψ Y) (hCL : L ⊓ Subgroup.centralizer (N : Set G) ≤ pCoreOf 2 L)
    {d : G} (hd : d ∈ L) {r : ℕ} (hr : Odd r) (hdr : d ^ r = 1) {x : ↥N} (hx : Y x ≠ 1)
    (hfix : d * x * d⁻¹ = x) : d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := autHom hc.le_normalizer ⟨d, hd⟩ with ha
  have hax : ((a : ↥(autOn L N)) : MulAut ↥N) x = x :=
    Subtype.ext (by rw [ha, autHom_apply_coe]; exact hfix)
  have hAv : ((ψ a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y x)) =
      Multiplicative.toAdd (Y x) := by
    rw [ha, ← hc.toAdd_Y_conj hd x, ← ha, hax]
  have hv : Multiplicative.toAdd (Y x) ≠ 0 := fun h0 => hx (by simpa using h0)
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hA2 : ψ a * ψ a = 1 :=
    Subtype.ext (sl2_mul_self_eq_one_of_fix h2F _ (ψ a).2 hv hAv)
  have hAr : ψ a ^ r = 1 := by
    rw [← map_pow, ha, ← map_pow]
    have hdr' : (⟨d, hd⟩ : ↥L) ^ r = 1 := Subtype.ext (by simpa using hdr)
    rw [hdr', map_one, map_one]
  have hone : a = 1 :=
    ψ.injective (by rw [eq_one_of_mul_self_of_pow_odd hA2 hr hAr, map_one])
  have hdC := mem_centralizer_of_autHom_eq_one hc.le_normalizer hone
  exact eq_one_of_mem_of_pow_odd (pCoreOf_isPGroup 2 L) (hCL ⟨hd, hdC⟩) hr hdr

end Nat

section Orth

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative MatrixGroups Matrix
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL unipSL_mul_self)

variable {G : Type} [Group G] [Finite G]

theorem IsOrthCh5.eq_one_of_fix_coprime {L W S : Subgroup G} {m r : ℕ}
    (hW : IsOrthCh5 L W (2 * m)) (hS : IsSylowTwoOf S L)
    (hC2 : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (W : Set G))) {d w : G}
    (hd : d ∈ L ⊓ Subgroup.normalizer (S : Set G)) (hr : Odd r) (hrm : Nat.Coprime r (2 ^ m + 1))
    (hdr : d ^ r = 1) (hd1 : d ≠ 1) (hw : w ∈ W) (hwS : w ∈ Subgroup.centralizer (S : Set G))
    (hdw : d * w * d⁻¹ = w) : w = 1 := by
  by_contra hw1
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hW.le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, -, -, hYint, hP, hline, hy0⟩ := hW.exists_lineCoord hS
  have hw1' : (⟨w, hw⟩ : ↥W) ≠ 1 := fun h0 => hw1 (congrArg Subtype.val h0)
  obtain ⟨h01, h10, h11⟩ := hline ⟨w, hw⟩ hwS
  have hy := hy0 ⟨w, hw⟩ hwS hw1'
  set xd := autHom hLW ⟨d, hd.1⟩ with hxd
  have hxdN : (xd : MulAut ↥W) ∈
      Subgroup.normalizer ((autOn S W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    conjAct_mem_normalizer_autOn ⟨d, hLW hd.1⟩ hd.2
  have hxd10 := upper_of_mem_normalizer ψ hP xd hxdN
  set c := (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have hpr : ψ xd ^ r = 1 := by
    rw [hxd, ← map_pow, ← map_pow]
    have h1 : (⟨d, hd.1⟩ : ↥L) ^ r = 1 := Subtype.ext (by simpa using hdr)
    rw [h1, map_one, map_one]
  have hcr : c ^ r = 1 := by
    have h2 := (upper_pow hxd10 r).2
    rw [hpr] at h2
    simpa using h2.symm
  have hc1 : c ≠ 1 := by
    intro hc1
    have hU := eq_unipSL_of_upper hxd10 hc1
    have h2 : ψ xd * ψ xd = 1 := by rw [hU]; exact unipSL_mul_self _
    have h5 : xd = 1 :=
      ψ.injective (by rw [eq_one_of_mul_self_of_pow_odd h2 hr hpr, map_one])
    have hdC := mem_centralizer_of_autHom_eq_one hLW h5
    exact hd1 (eq_one_of_mem_of_pow_odd hC2 ⟨hd.1, hdC⟩ hr hdr)
  have hcq : c * c ^ 2 ^ m ≠ 1 := by
    intro hcq
    apply hc1
    have h1 : c ^ (2 ^ m + 1) = 1 := by rw [pow_succ']; exact hcq
    have h2 := pow_gcd_eq_one.mpr ⟨hcr, h1⟩
    rwa [Nat.Coprime.gcd_eq_one hrm, pow_one] at h2
  have hfix : (xd : MulAut ↥W) ⟨w, hw⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [hxd, autHom_apply_coe]
    exact hdw
  have h1 := hYint xd ⟨w, hw⟩
  rw [hfix] at h1
  have h2 := congrFun (congrFun h1 0) 0
  rw [(twist_upper m hxd10 h01 h10 h11).1, ← hc] at h2
  have h3 : (c * c ^ 2 ^ m - 1) * (Multiplicative.toAdd (Y ⟨w, hw⟩)) 0 0 = 0 := by
    linear_combination -h2
  exact hy ((mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hcq))

end Orth

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped MatrixGroups

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem false_of_seven (h513 : Stmt5_1_3) (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {y : G}
    (hyD : y ∈ D) (hy1 : y ≠ 1) (hy7 : y ^ 7 = 1)
    (hyZ : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hyB : y ∈ borelL T L := hD.1 hyD
  have hyL : y ∈ L := hyB.1
  have hr : Odd 7 := by decide
  have hn2 : n ≠ 2 := by
    intro hn
    have hcard := (h.isCyclic_card_of_isHall l2TorusFact hD).2
    rw [hn] at hcard
    have h1 := orderOf_dvd_natCard (⟨y, hyD⟩ : ↥D)
    rw [hcard, Subgroup.orderOf_mk] at h1
    have h2 : orderOf y ∣ Nat.gcd 7 (2 ^ 2 - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy7) h1
    rw [show Nat.gcd 7 (2 ^ 2 - 1) = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact hy1 h2
  have hred := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hVT : V ≤ T := h.V_le_T hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVne : V ≠ ⊥ := fun hb => hV.2.2 (by rw [hb]; exact Subgroup.commutator_bot_left L)
  have hS := h.isSylowTwoOf_inf
  rcases h513 G T M L V n h hV with ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, hW₁, hW₂⟩ |
    ⟨hn2', -, -⟩ | h3 | h4 | ⟨-, h5', -⟩
  ·
    obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel le_rfl hVT hTV hVne
    have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hVel.1.is_comm.comm ⟨a, hsup ▸ Subgroup.mem_sup_left ha⟩
        ⟨b, hsup ▸ Subgroup.mem_sup_right hb⟩ |> congrArg Subtype.val
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hzV)
    have hfix : y * (a * b) * y⁻¹ = a * b := by
      rw [← Subgroup.mem_centralizer_iff.mp hyZ (a * b) hzZ, mul_inv_cancel_right]
    have hya : y * a * y⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hyL) a).mp ha
    have hyb : y * b * y⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hL₂ hyL) b).mp hb
    have hab := eq_of_mul_eq hdisj hya ha hyb hb (by rw [← hfix]; group)
    by_cases ha1 : a = 1
    · have hb1 : b ≠ 1 := fun hb1 => hz1 (by rw [ha1, hb1, mul_one])
      exact h.conj_ne_of_isNatModCh5_odd hW₂ hyL hr hy7 hy1 hb hb1 hab.2
    · exact h.conj_ne_of_isNatModCh5_odd hW₁ hyL hr hy7 hy1 ha ha1 hab.1
  · exact hn2 hn2'
  ·
    set N := ⁅V, L⁆ with hNdef
    have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
    have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
      le_normalizer_commutator_of hTV h.T_le_normalizer
    obtain ⟨F, _, _, _, -, ψ, Y, hc⟩ := h3.exists_qcoord hS
    have hNL : ⁅N, L⁆ ≠ ⊥ := fun hb =>
      hc.not_le_centralizer (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
    have hCL := h.inf_centralizer_le hc.le_normalizer hNL
    have hNne : N ≠ ⊥ := hV.2.2
    obtain ⟨z, hzN, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel hNV hVT hTN hNne
    have hzC : z ∉ Subgroup.centralizer (L : Set G) := fun hzC => hz1 (by
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzC⟩
      rwa [hZL, Subgroup.mem_bot] at hmem)
    have hY : Y ⟨z, hzN⟩ ≠ 1 := fun hY => hzC ((hc.ker _).mp hY)
    have hfix : y * z * y⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hyZ z hzZ, mul_inv_cancel_right]
    exact hy1 (hc.eq_one_of_fix_odd hCL hyL hr hy7 hY hfix)
  ·
    obtain ⟨k, hk, -⟩ := id h4
    obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel le_rfl hVT hTV hVne
    have hzS : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)
        (quasithinOmegaOneCenter_le_inf T hzZ).2
    have hC2 : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
      (pCoreOf_isPGroup 2 L).to_le (h.inf_centralizer_le hLV hV.2.2)
    have hfix : y * z * y⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hyZ z hzZ, mul_inv_cancel_right]
    exact hz1 (IsOrthCh5.eq_one_of_fix_coprime (hk ▸ h4) hS hC2 hyB hr
      (coprime_seven_two_pow_add_one k) hy7 hy1 hzV hzS hfix)
  · exact hn2 (h.n_eq_two_of_isBarS5 hV h5')

end Hyp5_0_1

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem exists_seven (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h510 : Stmt5_1_10)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hc5 : Case5_512 T H X Kh₁)
    (hcl : conjClosure Kh₁ T = Kh₁) (hJ : IsSporadic .J1 ↥(o2Img X Kh₁))
    (h7 : ∀ d ∈ o2Img X (D ⊓ X),
      d ^ 7 ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)))
    (hn3 : ¬ ∀ d ∈ o2Img X (D ⊓ X), ∃ k : ℕ,
      d ^ (3 ^ k) ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) :
    ∃ y ∈ D, y ∈ Kh₁ ∧ y ≠ 1 ∧ y ^ 7 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHX : H ≤ X := m.inH.1
  have hTX : T ≤ X := hTH.1.trans hHX
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hKX : oTwoUpper H ≤ X := (oTwoUpper_le H).trans hHX
  have hKKh : oTwoUpper H ≤ Kh₁ := m.lt.le.trans hcl.le
  have hXN : X ≤ Subgroup.normalizer (Kh₁ : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 m.inH.2 hTXs m.hat.1
    rwa [hcl] at this
  obtain ⟨-, -, hBorel, hHall, -⟩ := h510 G T M L H B D n m.hyp m.nota
  rw [m.hyp.borel_eq hBorel] at hHall
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hB3 : Nat.card B = 3 := by
    have := (isCyclic_card_of_isHall_borelOf le_rfl hc5.1 hTK hHall).2
    norm_num at this
    exact this
  have hBne : B ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hb3 : b ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨b, hbB⟩ : ↥B)
    rw [hB3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hbK : b ∈ oTwoUpper H := (hHall.1 hbB).1
  have hbKh : b ∈ Kh₁ := hKKh hbK
  have hbX : b ∈ X := hKX hbK
  have hbD : b ∈ Subgroup.normalizer (D : Set G) := m.nota.2.2 hbB
  push Not at hn3
  obtain ⟨xb, hxb, hk⟩ := hn3
  obtain ⟨⟨x, hxX⟩, hxDX, rfl⟩ := Subgroup.mem_map.mp hxb
  have hxD : x ∈ D := (Subgroup.mem_subgroupOf.mp hxDX).1
  set xb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨x, hxX⟩ : ↥X) with hxbdef
  set Q := o2Img X Kh₁ with hQ
  have hQN : ∀ g : O2Q X, g ∈ Subgroup.normalizer (Q : Set (O2Q X)) := by
    intro g
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) g
    exact o2Map_mem_normalizer (hXN x'.2)
  have : Q.Normal := ⟨fun k hk g => (Subgroup.mem_normalizer_iff.mp (hQN g) k).mp hk⟩
  obtain ⟨e⟩ := hJ
  obtain ⟨q, hq⟩ := exists_eq_conj_of_j1 e (MulAut.conjNormal xb)
  have hqk : ∀ k : ↥Q, xb * (k : O2Q X) * xb⁻¹ = ((q * k * q⁻¹ : ↥Q) : O2Q X) := by
    intro k
    rw [← MulAut.conjNormal_apply, hq, MulAut.conj_apply]
  have hq1 : q ≠ 1 := by
    intro hq1
    apply hk 0
    rw [pow_zero, pow_one, Subgroup.mem_centralizer_iff]
    intro k hkQ
    have h1 := hqk ⟨k, hkQ⟩
    simp only [hq1, one_mul, inv_one, mul_one] at h1
    calc k * xb = xb * k * xb⁻¹ * xb := by rw [h1]
      _ = xb * k := by group
  have hq7 : q ^ 7 = 1 := by
    have hc7 : MulAut.conj (q ^ 7) = 1 := by
      rw [map_pow, ← hq, ← map_pow]
      ext k
      have hc := Subgroup.mem_centralizer_iff.mp (h7 xb hxb) k k.2
      rw [MulAut.conjNormal_apply, MulAut.one_apply, ← hc, mul_inv_cancel_right]
    apply eq_one_of_forall_commute_of_j1 e
    intro k
    have h1 := congrArg (fun f : MulAut ↥Q => f k) hc7
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc q ^ 7 * k = q ^ 7 * k * (q ^ 7)⁻¹ * q ^ 7 := by group
      _ = k * q ^ 7 := by rw [h1]
  have hq30 : Nat.Coprime (orderOf q) 30 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hq7) (by norm_num)
  set bb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨b, hbX⟩ : ↥X) with hbbdef
  have hbbQ : bb ∈ Q := ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hbKh, rfl⟩
  have hb3' : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hbb3 : orderOf (⟨bb, hbbQ⟩ : ↥Q) = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show bb ^ 3 = 1
      rw [hbbdef, ← map_pow, hb3', map_one]
    · intro h1
      apply hb1'
      have h2 : bb = 1 := congrArg Subtype.val h1
      rw [hbbdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 := eq_one_of_mem_of_pow_odd (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) h2
        (by decide : Odd 3) hb3'
      exact congrArg Subtype.val h3
  have hyD : x * b * x⁻¹ * b⁻¹ ∈ D := by
    have h1 : b * x⁻¹ * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hbD x⁻¹).mp (D.inv_mem hxD)
    rw [show x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) by group]
    exact D.mul_mem hxD h1
  have hyKh : x * b * x⁻¹ * b⁻¹ ∈ Kh₁ :=
    Kh₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN hxX) b).mp hbKh) (Kh₁.inv_mem hbKh)
  have hyX : x * b * x⁻¹ * b⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem hxX hbX) (X.inv_mem hxX)) (X.inv_mem hbX)
  refine ⟨x * b * x⁻¹ * b⁻¹, hyD, hyKh, ?_, ?_⟩
  ·
    intro h1
    have hxbx : x * b * x⁻¹ = b := by
      calc x * b * x⁻¹ = x * b * x⁻¹ * b⁻¹ * b := by group
        _ = b := by rw [h1, one_mul]
    have h2 : xb * bb * xb⁻¹ = bb := by
      have h3 : (⟨x, hxX⟩ * ⟨b, hbX⟩ * (⟨x, hxX⟩ : ↥X)⁻¹ : ↥X) = ⟨b, hbX⟩ := Subtype.ext hxbx
      rw [hxbdef, hbbdef, ← map_inv, ← map_mul, ← map_mul, h3]
    have h3 := hqk ⟨bb, hbbQ⟩
    rw [h2] at h3
    have h4 : (⟨bb, hbbQ⟩ : ↥Q) = q * ⟨bb, hbbQ⟩ * q⁻¹ := Subtype.ext h3
    have hcomm : q * ⟨bb, hbbQ⟩ = ⟨bb, hbbQ⟩ * q := by
      calc q * ⟨bb, hbbQ⟩ = q * ⟨bb, hbbQ⟩ * q⁻¹ * q := by group
        _ = ⟨bb, hbbQ⟩ * q := by rw [← h4]
    exact hq1 (eq_one_of_commute_of_j1 e hq30 hbb3 hcomm)
  ·
    set y := x * b * x⁻¹ * b⁻¹ with hydef
    set yb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨y, hyX⟩ : ↥X) with hybdef
    have hybD : yb ∈ o2Img X (D ⊓ X) :=
      ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr ⟨hyD, hyX⟩, rfl⟩
    have hybQ : yb ∈ Q := ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr hyKh, rfl⟩
    have hyb7 : yb ^ 7 = 1 := by
      have h1 := eq_one_of_forall_commute_of_j1 e (z := ⟨yb ^ 7, Q.pow_mem hybQ 7⟩)
        (fun k => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (h7 yb hybD) k k.2).symm))
      exact congrArg Subtype.val h1
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ((⟨y, hyX⟩ : ↥X) ^ 7) = 1 := by
      rw [map_pow]
      exact hyb7
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥X).map X.subtype) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map _
    have hmem : y ^ 7 ∈ (CFSG.pCore 2 ↥X).map X.subtype := ⟨_, h2, by simp⟩
    exact eq_one_of_mem_of_mem_odd hP m.nota.2.1.2.1 hmem (D.pow_mem hyD 7)

end Main513

theorem stmt5_1_13_type_j1_ZK_of (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h510 : Stmt5_1_10) (h513 : Stmt5_1_3)
    (h432 : Stmt4_3_2) : Stmt5_1_13_type_j1_ZK := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl hJ h7 hn3 hZK
  have h := m.hyp.toHyp5_0_1
  set Z := quasithinOmegaOneCenter T with hZdef
  have hKhZ : Kh₁ ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZK)
  obtain ⟨y, hyD, hyK, hy1, hy7⟩ := m.exists_seven h37 h38 h510 hc5 hcl hJ h7 hn3
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hTH
  have hKZ : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) :=
    (m.lt.le.trans hcl.le).trans hKhZ
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) :=
    hKT ▸ sup_le hKZ (Main513.T_le_centralizer_omega T)
  exact h.false_of_seven h513 m.module m.nota.2.1 (m.inf_centralizer_eq_bot h432 hHZ) hyD hy1
    hy7 (hKhZ hyK)

end CFSG.Quasithin.H13
