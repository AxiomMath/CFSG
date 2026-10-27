module

public import CFSG.Walter.Bender1970.S2.Basic
import CFSG.StronglyEmbedded.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Walter.PSL2Facts.OddMaximal

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

theorem isSolvable_dihedralGroup' (z : ℕ) [NeZero z] : Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have hRsolv : Group.IsSolvable R := by
    have : IsCyclic R := Subgroup.isCyclic_zpowers _
    let : CommGroup R := IsCyclic.commGroup
    infer_instance
  have hRcard : Nat.card R = z := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
    exact (Nat.eq_of_mul_eq_mul_right hz h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_of_sup_eq_top {G : Type*} [Group G] {N C : Subgroup G} [N.Normal]
    (hN : IsMulCommutative N) (hC : IsMulCommutative C) (hsup : N ⊔ C = ⊤) :
    Group.IsSolvable G := by
  have hNs : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => hN.is_comm.comm a b
  have hCs : Group.IsSolvable C := Group.isSolvable_of_comm fun a b => hC.is_comm.comm a b
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x ∈ C ⊔ N := by rw [sup_comm, hsup]; exact Subgroup.mem_top x
    obtain ⟨c, hc, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using N.inv_mem hn
  have hQ : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem odd_two_pow_sq_sub_one {m : ℕ} (hm : m ≠ 0) : Odd ((2 ^ m) ^ 2 - 1) := by
  have h1 : Even ((2 ^ m) ^ 2) :=
    Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hm⟩, two_ne_zero⟩
  have h2 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  obtain ⟨k, hk⟩ := h1
  exact Nat.odd_iff.mpr (by omega)

theorem le_of_two_pow_dvd {f m : ℕ} (hm : m ≠ 0) (h : 2 ^ f ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1)) :
    f ≤ m := by
  have hcop : Nat.Coprime (2 ^ f) ((2 ^ m) ^ 2 - 1) :=
    Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr (odd_two_pow_sq_sub_one hm))
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h)

theorem psl2_even_isSolvable_of_sylow_le {f : ℕ} (hf : 2 ≤ f)
    (U : Sylow 2 PSL(2, GaloisField 2 f)) {Y : Subgroup PSL(2, GaloisField 2 f)}
    (hUY : (U : Subgroup PSL(2, GaloisField 2 f)) ≤ Y) (hY : Y ≠ ⊤) :
    Group.IsSolvable Y := by
  have hFc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hdvd : 2 ^ f ∣ Nat.card Y := (psl2_even_sylow_two hf U).2 ▸ Subgroup.card_dvd_of_le hUY
  have hcardL : Nat.card PSL(2, GaloisField 2 f) = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
    psl2_even_card (by omega)
  have htop : Nat.card Y = 2 ^ f * ((2 ^ f) ^ 2 - 1) → False := fun h =>
    hY (Subgroup.eq_top_of_card_eq Y (h.trans hcardL.symm))
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFc Y with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hYz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, s, -, -, N, C, hN, hNel, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, ⟨e⟩⟩
  · exact Group.isSolvable_of_comm fun a b => hEl.toIsMulCommutative.is_comm.comm a b
  · let : CommGroup Y := IsCyclic.commGroup
    infer_instance
  · have : NeZero z := ⟨fun hz0 => by
      rw [hz0, mul_zero] at hYz
      exact Nat.card_pos.ne' hYz⟩
    have := isSolvable_dihedralGroup' z
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exfalso
    have h60 : Nat.card Y = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [h60] at hdvd
    have hf2 : f = 2 := by
      by_contra hf2
      have h8 : 2 ^ 3 ∣ 2 ^ f := pow_dvd_pow 2 (by omega)
      have := h8.trans hdvd
      norm_num at this
    apply htop
    rw [h60, hf2]
    norm_num
  · have : N.Normal := hN
    let : CommGroup C := IsCyclic.commGroup
    exact isSolvable_of_sup_eq_top hNel.toIsMulCommutative
      ⟨⟨fun a b => mul_comm a b⟩⟩ hsup
  · exfalso
    have hYc : Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact psl2_even_card hm
    have hfm : f ≤ m := le_of_two_pow_dvd hm (hYc ▸ hdvd)
    have hmf' : m = f := le_antisymm (Nat.le_of_dvd (by omega) hmf) hfm
    apply htop
    rw [hYc, hmf']
  · exfalso
    have hYc : Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      have := pgl2_card_formula (GaloisField 2 m)
      rwa [GaloisField.card 2 m hm] at this
    have hfm : f ≤ m := le_of_two_pow_dvd hm (hYc ▸ hdvd)
    have h2m : 2 * m ≤ f := Nat.le_of_dvd (by omega) hmf
    omega

theorem nonempty_psl2_five_mulEquiv_psl2_four [Fact (Nat.Prime 5)] :
    Nonempty (PSL(2, GaloisField 5 1) ≃* PSL(2, GaloisField 2 2)) := by
  have h5c : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  have h4c : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 two_ne_zero
  have h5 : Nat.card PSL(2, GaloisField 5 1) = 60 := by
    rw [psl2_card_formula _ (isOddPrimePower_of_card h5c (by decide) one_pos), h5c]
    norm_num
  have h4 : Nat.card PSL(2, GaloisField 2 2) = 60 := by
    rw [psl2_even_card two_ne_zero]
    norm_num
  have : IsSimpleGroup PSL(2, GaloisField 5 1) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [h5c]; norm_num)
  have : IsSimpleGroup PSL(2, GaloisField 2 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [h4c]; norm_num)
  obtain ⟨e5⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h5
  obtain ⟨e4⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h4
  exact ⟨e5.trans e4.symm⟩

theorem isTypeL2Even_of_mulEquiv_psl2_five
    {L : Type*} [Group L] {p f : ℕ} [Fact p.Prime]
    (hf : 0 < f) (hq : p ^ f = 5) (e : L ≃* PSL(2, GaloisField p f)) : IsTypeL2Even L := by
  have hpd : p ∣ 5 := hq ▸ dvd_pow_self p hf.ne'
  have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpd
  subst hp5
  have hf1 : f = 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 5) (show 5 ^ f = 5 ^ 1 by rw [hq, pow_one])
  subst hf1
  obtain ⟨e'⟩ := nonempty_psl2_five_mulEquiv_psl2_four
  exact ⟨2, le_rfl, ⟨e.trans e'⟩⟩

theorem isSolvable_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (Y : Subgroup A)
    (h : Group.IsSolvable (Y.map e.toMonoidHom)) : Group.IsSolvable Y :=
  Group.isSolvable_of_surjective (f := (Y.equivMapOfInjective e.toMonoidHom e.injective).symm
    |>.toMonoidHom) (MulEquiv.surjective _)

theorem IsTypeL2.isSolvable_of_centralizer_le
    {L : Type*} [Group L] [Finite L]
    (hL : IsTypeL2 L) {u : L} (hu : orderOf u = 2) {Y : Subgroup L}
    (hCY : Subgroup.centralizer ({u} : Set L) ≤ Y) (hY : Y ≠ ⊤) : Group.IsSolvable Y := by
  have heven : IsTypeL2Even L → Group.IsSolvable Y := by
    rintro ⟨f, hf, ⟨e⟩⟩
    apply isSolvable_map_mulEquiv e Y
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hu' : orderOf (e u) = 2 := by rwa [MulEquiv.orderOf_eq]
    have hp : IsPGroup 2 (Subgroup.zpowers (e u)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu', pow_one])
    obtain ⟨U, hU⟩ := hp.exists_le_sylow
    have heu1 : e u ≠ 1 := by intro h; rw [h, orderOf_one] at hu'; omega
    have hCU := psl2_even_centralizer_involution hf U (hU (Subgroup.mem_zpowers _)) heu1
    refine psl2_even_isSolvable_of_sylow_le hf U ?_ ?_
    · rw [← hCU, ← map_centralizer_singleton_mulEquiv]
      exact Subgroup.map_mono hCY
    · intro h
      apply hY
      have h' := congrArg (Subgroup.map e.symm.toMonoidHom) h
      rwa [Subgroup.map_map, Subgroup.map_top_of_surjective _ e.symm.surjective,
        show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L by ext; simp,
        Subgroup.map_id] at h'
  rcases hL with heL | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩
  · exact heven heL
  · by_cases h11 : 11 ≤ p ^ f
    · apply isSolvable_map_mulEquiv e Y
      have hu' : orderOf (e u) = 2 := by rwa [MulEquiv.orderOf_eq]
      have hmax := psl2_odd_centralizer_involution_isCoatom hpodd hf h11 h8 hu'
      have hCY' : Subgroup.centralizer ({e u} : Set PSL(2, GaloisField p f)) ≤
          Y.map e.toMonoidHom := by
        rw [← map_centralizer_singleton_mulEquiv]
        exact Subgroup.map_mono hCY
      have hY' : Y.map e.toMonoidHom ≠ ⊤ := by
        intro h
        apply hY
        have h' := congrArg (Subgroup.map e.symm.toMonoidHom) h
        rwa [Subgroup.map_map, Subgroup.map_top_of_surjective _ e.symm.surjective,
          show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L by ext; simp,
          Subgroup.map_id] at h'
      rcases hmax.le_iff.mp hCY' with h | h
      · exact absurd h hY'
      · rw [h]
        obtain ⟨n, -, -, -, ⟨d⟩⟩ := psl2_centralizer_involution_dihedral _
          (GaloisField.card p f hf.ne') hpodd hf (by omega) hu'
        have : NeZero n := ⟨by rintro rfl; exact absurd (DihedralGroup.nat_card (n := 0)) (by
          rw [← Nat.card_congr d.toEquiv]; exact Nat.card_pos.ne')⟩
        have := isSolvable_dihedralGroup' n
        exact Group.isSolvable_of_surjective (f := d.symm.toMonoidHom) d.symm.surjective
    · exact heven (isTypeL2Even_of_mulEquiv_psl2_five hf (by omega) e)

end CFSG.Walter
