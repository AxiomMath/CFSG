module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec41
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trans
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem bar_card_mul_card_of_le {G : Type} [Group G] {M Q : Subgroup G}
    [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) :
    Nat.card (bar M Q S) * Nat.card Q = Nat.card S := by
  have hQM : Q ≤ M := hQS.trans hSM
  have hle : Q.subgroupOf M ≤ S.subgroupOf M := fun x hx => hQS hx
  have hS' : Nat.card (S.subgroupOf M) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  have hQ' : Nat.card ((Q.subgroupOf M).subgroupOf (S.subgroupOf M)) = Nat.card Q :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv)
  have h1 := Subgroup.card_ker_mul_card_range
    ((QuotientGroup.mk' (Q.subgroupOf M)).domRestrict (S.subgroupOf M))
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', hQ',
    hS'] at h1
  rw [Nat.mul_comm]
  exact h1

theorem Ctx.normal_bar_H0 {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) : (bar M Q (H0 M Z)).Normal := by
  have hN : ((H0 M Z).subgroupOf M).Normal := by
    refine ⟨fun x hx m => ?_⟩
    have hx' : (x : G) ∈ H0 M Z := hx
    show ((m * x * m⁻¹ : ↥M) : G) ∈ H0 M Z
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    · exact M.mul_mem (M.mul_mem m.2 x.2) (M.inv_mem m.2)
    · have hzm : (m : G)⁻¹ * z * (m : G) ∈ Z := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hc.hyp.Z_normal.2 m.2)) z).mp
          hz
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hx'.2 _ hzm
      calc z * ((m : G) * (x : G) * (m : G)⁻¹)
          = (m : G) * ((m : G)⁻¹ * z * (m : G) * (x : G)) * (m : G)⁻¹ := by group
        _ = (m : G) * ((x : G) * ((m : G)⁻¹ * z * (m : G))) * (m : G)⁻¹ := by rw [h1]
        _ = ((m : G) * (x : G) * (m : G)⁻¹) * z := by group
  exact bar_normal hN

theorem Ctx.card_bar_LB_of_34 {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) :
    Nat.card (bar M Q (LB M Q B)) = Nat.card Z ^ (n - 1) := by
  have hLB := (stroth_3_5 h34 hc hw hn hno hgen).2.2.1
  have h := bar_card_mul_card_of_le (M := M) (S := LB M Q B) le_sup_left hc.LB_le_M
  rw [hLB] at h
  have : Nat.card (bar M Q (LB M Q B)) * Nat.card Q = Nat.card Z ^ (n - 1) * Nat.card Q := by
    rw [h, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this

theorem Ctx.four_le_card_bar_LB {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) : 4 ≤ Nat.card (bar M Q (LB M Q B)) := by
  rw [hc.card_bar_LB_of_34 h34 hw hn hno hgen]
  calc 4 ≤ Nat.card Z := hc.hyp.q4
    _ = Nat.card Z ^ 1 := (pow_one _).symm
    _ ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right (by have := hc.hyp.q4; omega) (by omega)


section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.eq_bot_of_comm_odd [hN : (Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    (A : Subgroup (Mbar M Q)) (hAH : A ≤ bar M Q (H0 M Z)) (hodd : Odd (Nat.card A))
    (hcomm : ∀ x ∈ A, ∀ t : ↥M, (t : G) ∈ LB M Q B →
      x * (QuotientGroup.mk t : Mbar M Q) = (QuotientGroup.mk t : Mbar M Q) * x) : A = ⊥ := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφadd, hφsemi⟩ := exists_actionHom_M hc.hyp h
  obtain ⟨φ₀, hφ₀π, hφ₀ker, hφ₀Q⟩ := exists_actionHom_H0 hc.hyp h
  have hQnorm : ∀ {t : G}, t ∈ M → ∀ y ∈ Q, t * y * t⁻¹ ∈ Q := fun {t} ht y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ht) y).mp hy
  have hLH : LB M Q B ≤ H0 M Z := fun t ht => ⟨hc.LB_le_M ht, Subgroup.mem_centralizer_iff.mpr
    fun z hz => by
      have := hc.LB_centralizes_Z ht z hz
      calc z * t = (t * z * t⁻¹) * t := by rw [this]
        _ = t * z := by group⟩
  let Φ : Mbar M Q →* Equiv.Perm M₀.E :=
    QuotientGroup.lift (Q.subgroupOf M) φ (fun q hq => MonoidHom.mem_ker.mpr ((hφker q).mpr hq))
  have hΦ : ∀ t : ↥M, Φ (QuotientGroup.mk t) = φ t := fun t => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ] at hx
    exact (QuotientGroup.eq_one_iff t).mpr ((hφker t).mp hx)
  have hcompat : ∀ (t : ↥M) (u : ↥(H0 M Z)), (t : G) = (u : G) → ∀ e, φ t e = φ₀ u e := by
    intro t u htu e
    refine congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := (t : G)) (S₁ := φ t) (S₂ := φ₀ u)
      (hφπ t) (fun x hx => ?_)) e
    rw [htu]
    exact hφ₀π u x hx
  haveI : Finite M₀.E := Module.finite_of_finite (GaloisField 2 m)
  let ρ : ↥A →* Equiv.Perm M₀.E := Φ.comp A.subtype
  have hρinj : Function.Injective ρ := hΦinj.comp A.subtype_injective
  have hρadd : ∀ γ' e f, ρ γ' (e + f) = ρ γ' e + ρ γ' f := by
    intro γ' e f
    obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (γ' : Mbar M Q)
    show Φ (γ' : Mbar M Q) (e + f) = Φ (γ' : Mbar M Q) e + Φ (γ' : Mbar M Q) f
    rw [← ht, hΦ]
    exact hφadd t e f
  have hlinQ : ∀ γ' : ↥A, ∃ u : ↥(H0 M Z), ∀ e, ρ γ' e = φ₀ u e := by
    intro γ'
    obtain ⟨y, hy, hya⟩ := hAH γ'.2
    refine ⟨⟨(y : G), hy⟩, fun e => ?_⟩
    show Φ (γ' : Mbar M Q) e = _
    rw [← hya]
    exact hcompat y ⟨(y : G), hy⟩ rfl e
  have hρlin : ∀ γ' (c : GaloisField 2 m) e, ρ γ' (c • e) = c • ρ γ' e := by
    intro γ' c e
    obtain ⟨u, hu⟩ := hlinQ γ'
    rw [hu, hu, map_smul]
  have hρQ : ∀ γ' e, M₀.Qf (ρ γ' e) = M₀.Qf e := by
    intro γ' e
    obtain ⟨u, hu⟩ := hlinQ γ'
    rw [hu]
    exact hφ₀Q u e
  have hQnz : ∃ e, M₀.Qf e ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hb0
    refine M₀.nondeg b fun f => ?_
    have h1 := M₀.Qf_add b f
    rw [hcon, hcon, hcon] at h1
    exact (by simpa using h1.symm : M₀.B b f = 0)
  have hordodd : ∀ γ' : ↥A, Odd (orderOf γ') := fun γ' =>
    Odd.of_dvd_nat hodd (orderOf_dvd_natCard γ')
  let Λ : Subgroup (M₀.E ≃ₗ[GaloisField 2 m] M₀.E) := (φ₀.comp (Subgroup.inclusion hLH)).range
  have hΛ : IsPGroup 2 Λ := by
    intro g
    obtain ⟨T, t, rfl⟩ := g
    refine ⟨1, Subtype.ext ?_⟩
    show ((φ₀.comp (Subgroup.inclusion hLH)) t) ^ (2 ^ 1) = 1
    rw [← map_pow]
    exact (hφ₀ker (Subgroup.inclusion hLH (t ^ (2 ^ 1)))).mpr (by
      simpa using hc.sq_mem_Q_of_mem_LB t.2)
  have hle : B ⊔ Z ≤ M₀.lift (M₀.img B) := sup_le
    (fun b' hb' => ⟨hc.le hb', M₀.pi_mem_img hb' (hc.le hb')⟩)
    (fun z hz => ⟨hc.Z_le_Q hz, by
      rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]; exact AddSubgroup.zero_mem _⟩)
  have hLB_B : ∀ (t : ↥(LB M Q B)) (u : G), u ∈ B →
      φ₀ (Subgroup.inclusion hLH t) (M₀.π u) = M₀.π u := by
    intro t u hu
    rw [← hφ₀π _ u (hc.le hu)]
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) (hc.le hu)
      (hQnorm (hc.LB_le_M t.2) u (hc.le hu))).mp (hc.comm_B_mem_Z t.2 hu)
  have hfix : ∀ v : M₀.E, (∀ T ∈ Λ, T v = v) ↔ ∃ c : GaloisField 2 m, v = c • b := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
      have hx : x ∈ CQt Q Z (LB M Q B) := by
        refine ⟨hxQ, fun t ht => ?_⟩
        have hT : φ₀ (Subgroup.inclusion hLH ⟨t, ht⟩) ∈ Λ := ⟨⟨t, ht⟩, rfl⟩
        have := hv _ hT
        rw [← hφ₀π _ x hxQ] at this
        exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ
          (hQnorm (hc.LB_le_M ht) x hxQ)).mpr this
      rw [h35] at hx
      exact (hB _).mp (hle hx).2
    · rintro ⟨c, rfl⟩ T hT
      obtain ⟨t, rfl⟩ := hT
      obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
      have hTb : (φ₀.comp (Subgroup.inclusion hLH)) t b = b := by
        rw [← hu]; exact hLB_B t u huB
      rw [map_smul, hTb]
  have hcomm' : ∀ γ' : ↥A, ∀ T ∈ Λ, ∀ e, ρ γ' (T e) = T (ρ γ' e) := by
    intro γ' T hT e
    obtain ⟨t, rfl⟩ := hT
    let t' : ↥M := ⟨t, hc.LB_le_M t.2⟩
    have hcm := hcomm γ' γ'.2 t' t.2
    have h1 : Φ (γ' : Mbar M Q) * Φ (QuotientGroup.mk t') =
        Φ (QuotientGroup.mk t') * Φ (γ' : Mbar M Q) := by
      rw [← map_mul, ← map_mul, hcm]
    have h2 : ∀ e, Φ (QuotientGroup.mk t') e = (φ₀.comp (Subgroup.inclusion hLH)) t e :=
      fun e => hcompat t' (Subgroup.inclusion hLH t) rfl e
    calc ρ γ' ((φ₀.comp (Subgroup.inclusion hLH)) t e)
        = ρ γ' (Φ (QuotientGroup.mk t') e) := by rw [h2]
      _ = (Φ (γ' : Mbar M Q) * Φ (QuotientGroup.mk t')) e := rfl
      _ = (Φ (QuotientGroup.mk t') * Φ (γ' : Mbar M Q)) e := by rw [h1]
      _ = Φ (QuotientGroup.mk t') (ρ γ' e) := rfl
      _ = (φ₀.comp (Subgroup.inclusion hLH)) t (ρ γ' e) := h2 _
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have := eq_one_of_commutes_odd ρ hρinj hρadd hρlin M₀.Qf M₀.Qf_smul hρQ hQnz hordodd Λ hΛ b
    hb0 hfix hcomm' ⟨x, hx⟩
  exact congrArg Subtype.val this

theorem Ctx.weaklyClosed_bar_LB [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (x : Mbar M Q)
    (hx : conjSubgroup x (bar M Q (LB M Q B)) ≤
      Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q))) :
    conjSubgroup x (bar M Q (LB M Q B)) = bar M Q (LB M Q B) := by
  have h := weaklyClosed_bar_of_weaklyClosed (le_sup_left : Q ≤ LB M Q B) hc.LB_le_M
    (fun _ hm h => hc.weaklyClosed_of_3_1 hw hn hno hm h) x⁻¹ (by rwa [inv_inv])
  rwa [inv_inv] at h

theorem Ctx.inter_bar_LB_ne_bot [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) {X : Subgroup (Mbar M Q)} (hXq : CFSG.IsQuasisimple X)
    (hXn : bar M Q (LB M Q B) ≤ Subgroup.normalizer (X : Set (Mbar M Q))) :
    bar M Q (LB M Q B) ⊓ X ≠ ⊥ := by
  intro h0
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  have hcomm := comm_of_inter_eq_bot hc.isElemAbelian_bar_LB
    (hc.weaklyClosed_bar_LB hw hn hno) hXn hXq h0
  exact hc.false_of_comm h35 X hXq fun x hx t ht =>
    hcomm x hx _ (Subgroup.mem_map_of_mem _ (show t ∈ (LB M Q B).subgroupOf M from ht))

end

theorem mk_mem_bar_iff_sec4 {G : Type} [Group G] {M Q : Subgroup G}
    [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S) (y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q S ↔ (y : G) ∈ S := by
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    have h1 : s⁻¹ * y ∈ Q.subgroupOf M := QuotientGroup.eq.mp hsy
    have h2 : (s : G)⁻¹ * y ∈ S := hQS h1
    have e : (y : G) = s * ((s : G)⁻¹ * y) := by group
    rw [e]
    exact S.mul_mem hs h2
  · intro hy
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩

theorem mk_mem_conj_bar_iff_sec4 {G : Type} [Group G] {M Q : Subgroup G}
    [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S) (m y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q S) ↔
      (y : G) ∈ conjSubgroup (m : G) S := by
  rw [mem_conjSubgroup, mem_conjSubgroup, ← map_inv, ← map_mul, ← map_mul,
    mk_mem_bar_iff_sec4 hQS]
  rfl

end CFSG.RankThree.GF2n.Stroth80
