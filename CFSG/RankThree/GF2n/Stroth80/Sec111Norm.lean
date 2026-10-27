module

public import CFSG.RankThree.GF2n.Stroth80.Sec12LBFlag
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Perp
public import CFSG.RankThree.GF2n.Stroth80.Sec11LinAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.mem_normalizer_LB_of_normalizer (hc : Ctx M Q Z B) {a : G} (haM : a ∈ M)
    (haV : a ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G)) :
    a ∈ Subgroup.normalizer (LB M Q B : Set G) := by
  have hc' := hc.conj_of_mem haM
  have hVa : conjSubgroup a (B ⊔ Z : Subgroup G) = B ⊔ Z := conjSubgroup_eq_self_iff.mpr haV
  have hle : conjSubgroup a B ≤ Z ⊔ B := by
    have h1 : conjSubgroup a B ≤ conjSubgroup a (B ⊔ Z : Subgroup G) :=
      Subgroup.map_mono le_sup_left
    rw [hVa, sup_comm] at h1
    exact h1
  obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB hc' hle
  have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
  have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
  refine conjSubgroup_eq_self_iff.mp ?_
  rw [← hc.LB_conj haM, ← hpB, hc.LB_conj hpM, hLp]

theorem Ctx.mem_sup_of_comm_LB (hc : Ctx M Q Z B) {x : G} (hx : x ∈ Q ⊓ QB B)
    (hcomm : ∀ t ∈ LB M Q B, ⁅t, x⁆ ∈ Z) : x ∈ (Z ⊔ B : Subgroup G) := by
  by_contra hnot
  obtain ⟨c, hcB, hc1⟩ := hc.exists_ne_one_B
  obtain ⟨s, hs, hsx⟩ := hc.exists_mem_QB_M_comm_eq hx.2 hnot hcB
  have hsL : s ∈ LB M Q B := Subgroup.mem_sup_right hs
  have hcZ : c ∈ Z := hsx ▸ hcomm s hsL
  have hmem : c ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hcZ, hcB⟩
  rw [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
  exact hc1 hmem


theorem Ctx.card_LB_le_of_LB_eq (hcB : Ctx M Q Z B) {A : Subgroup G}
    (hcA : Ctx M Q Z A) (hLAB : LB M Q A = LB M Q B) (hne : ¬ A ≤ B ⊔ Z) :
    Nat.card (LB M Q B) ≤ Nat.card Q * Nat.card Z := by
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hcB.hyp
  obtain ⟨b, hb0, hbs, hB, hcentB, -⟩ := hcB.dictB h
  obtain ⟨a, ha0, has, hA, hcentA, -⟩ := hcA.dictB h
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hcB.hyp h
  have hZQ : Z ≤ Q := hcB.Z_le_Q
  have hab : ∀ c : GaloisField 2 m, c • b ≠ a := by
    intro c hc
    apply hne
    intro x hxA
    have hxQ : x ∈ Q := hcA.le hxA
    obtain ⟨s, hs⟩ := (hA _).mp (M₀.pi_mem_img hxA hxQ)
    have hxB : M₀.π x ∈ M₀.img B := (hB _).mpr ⟨s * c, by rw [hs, ← hc, smul_smul]⟩
    exact (M₀.mem_img_iff (le_sup_right : Z ≤ B ⊔ Z) hxQ).mp (M₀.img_mono le_sup_left hxB)
  have key : ∀ c c' : GaloisField 2 m, c • b = c' • a → c = 0 := by
    intro c c' hcc
    by_contra hc0
    by_cases hc'0 : c' = 0
    · rw [hc'0, zero_smul] at hcc
      rcases smul_eq_zero.mp hcc with h1 | h1
      · exact hc0 h1
      · exact hb0 h1
    · apply hab (c'⁻¹ * c)
      rw [mul_smul, hcc, smul_smul, inv_mul_cancel₀ hc'0, one_smul]
  have hlift : ∀ S : Subgroup G, S ≤ Q → (S ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img S) := by
    intro S hSQ
    refine sup_le (fun u hu => ⟨hSQ hu, M₀.pi_mem_img hu (hSQ hu)⟩) (fun z hz => ?_)
    refine ⟨h.reg.V_le hz, ?_⟩
    rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  let Tl : ↥(LB M Q B) → (M₀.E →ₗ[GaloisField 2 m] M₀.E) := fun t =>
    ((φ ⟨t, hcB.LB_le_H0 t.2⟩ : M₀.E ≃ₗ[GaloisField 2 m] M₀.E) :
      M₀.E →ₗ[GaloisField 2 m] M₀.E)
  have hTπ : ∀ (t : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((t : G) * x * (t : G)⁻¹) = Tl t (M₀.π x) := fun t x hx =>
    hφπ ⟨t, hcB.LB_le_H0 t.2⟩ x hx
  have hTiso : ∀ (t : ↥(LB M Q B)) e, M₀.Qf (Tl t e) = M₀.Qf e := fun t e =>
    hφiso ⟨t, hcB.LB_le_H0 t.2⟩ e
  have htA : ∀ t : ↥(LB M Q B), (t : G) ∈ LB M Q A := fun t => by rw [hLAB]; exact t.2
  have hLB := fun t : ↥(LB M Q B) => hcB.LB_act_fix_line h hB t.2 (T := Tl t) (hTπ t)
  have hLA' := fun t : ↥(LB M Q B) => hcA.LB_act_fix_line h hA (htA t) (T := Tl t) (hTπ t)
  have htM : ∀ t : ↥(LB M Q B), (t : G) ∈ M := fun t => hcB.LB_le_M t.2
  have hconjQ : ∀ (t : ↥(LB M Q B)) (x : G), x ∈ Q → (t : G) * x * (t : G)⁻¹ ∈ Q := fun t x hx =>
    (Subgroup.mem_normalizer_iff.mp (hcB.hyp.Q_normal.2 (htM t)) x).mp hx
  have hP2 : ∀ x ∈ Q, x ∈ QB A → x ∈ QB B → x ∈ Z := by
    intro x hxQ hxA hxB
    have hfix : ∀ t : ↥(LB M Q B), Tl t (M₀.π x) = M₀.π x := by
      intro t
      obtain ⟨c, hc⟩ := (hLB t).2 (M₀.π x) (M₀.pi_mem_img ⟨hxQ, hxB⟩ hxQ)
      obtain ⟨c', hc'⟩ := (hLA' t).2 (M₀.π x) (M₀.pi_mem_img ⟨hxQ, hxA⟩ hxQ)
      have hc0 : c = 0 := key c c' (hc.symm.trans hc')
      rw [hc0, zero_smul, sub_eq_zero] at hc
      exact hc
    have hcomm : ∀ t ∈ LB M Q B, ⁅t, x⁆ ∈ Z := by
      intro t ht
      have := hfix ⟨t, ht⟩
      exact (M₀.comm_mem_iff hxQ (hconjQ ⟨t, ht⟩ x hxQ)).mpr ((hTπ ⟨t, ht⟩ x hxQ).trans this)
    have h1 : x ∈ (Z ⊔ B : Subgroup G) := hcB.mem_sup_of_comm_LB ⟨hxQ, hxB⟩ hcomm
    have h2 : x ∈ (Z ⊔ A : Subgroup G) :=
      hcA.mem_sup_of_comm_LB ⟨hxQ, hxA⟩ (fun t ht => hcomm t (hLAB ▸ ht))
    rw [sup_comm] at h1 h2
    obtain ⟨s, hs⟩ := (hB _).mp (hlift B hcB.le h1).2
    obtain ⟨s', hs'⟩ := (hA _).mp (hlift A hcA.le h2).2
    have hs0 : s = 0 := key s s' (hs.symm.trans hs')
    exact (M₀.π_ker x hxQ).mp (by rw [hs, hs0, zero_smul])
  have hU : ∀ (t : ↥(LB M Q B)) e, M₀.B e a = 0 → M₀.B e b = 0 → Tl t e = e := by
    intro t e hea heb
    obtain ⟨c, hcQ, rfl⟩ := M₀.π_surj e
    have hcB' : c ∈ Q ⊓ Subgroup.centralizer (B : Set G) := ⟨hcQ, (hcentB c hcQ).mpr heb⟩
    have hcA' : c ∈ Q ⊓ Subgroup.centralizer (A : Set G) := ⟨hcQ, (hcentA c hcQ).mpr hea⟩
    have h1 := hcB.comm_mem_inf_of_mem_LB t.2 hcB'
    have h2 := hcA.comm_mem_inf_of_mem_LB (htA t) hcA'
    have h3 : ⁅(t : G), c⁆ ∈ Z := hP2 _ h1.1 h2.2 h1.2
    have h4 := (M₀.comm_mem_iff hcQ (hconjQ t c hcQ)).mp h3
    rw [← hTπ t c hcQ]
    exact h4
  have hsc : ∀ t : ↥(LB M Q B), ∃ c : GaloisField 2 m,
      ∀ e, Tl t e = e + c • (M₀.B e b • a + M₀.B e a • b) := fun t =>
    Tim79.QuadModel.exists_scalar_of_fix_perp M₀ has hbs hb0 hab (hTiso t) (hLA' t).1 (hLB t).1
      (hU t)
  let ψ : ↥(LB M Q B) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E) :=
    φ.comp (Subgroup.inclusion hcB.LB_le_H0)
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hker : ψ.ker = Q.subgroupOf (LB M Q B) := by
    ext t
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφker ⟨t, hcB.LB_le_H0 t.2⟩
  have hcardker : Nat.card ψ.ker = Nat.card Q := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = Nat.card (LB M Q B) := by
    rw [← Subgroup.index_ker ψ]
    exact Subgroup.card_mul_index ψ.ker
  have hrange : ∀ T : ψ.range, ∃ c : GaloisField 2 m,
      ∀ e, (T : M₀.E ≃ₗ[GaloisField 2 m] M₀.E) e = e + c • (M₀.B e b • a + M₀.B e a • b) := by
    rintro ⟨T, t, rfl⟩
    exact hsc t
  have hle : Nat.card ψ.range ≤ Nat.card (GaloisField 2 m) := by
    refine Nat.card_le_card_of_injective (fun T => Classical.choose (hrange T)) ?_
    intro T T' hTT
    refine Subtype.ext (LinearEquiv.ext fun e => ?_)
    have h1 := Classical.choose_spec (hrange T) e
    have h2 := Classical.choose_spec (hrange T') e
    rw [h1, h2]
    simp only at hTT
    rw [hTT]
  rw [← hmul, hcardker, ← h.card]
  exact Nat.mul_le_mul_left _ hle

theorem stroth_11_1a (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) {m : G} (hm : m ∈ M) :
    m ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) ↔
      m ∈ Subgroup.normalizer (LB M Q B : Set G) := by
  refine ⟨hc.mem_normalizer_LB_of_normalizer hm, fun hmL => ?_⟩
  by_contra hmV
  have hcA : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hLAB : LB M Q (conjSubgroup m B) = LB M Q B := by
    rw [hc.LB_conj hm]
    exact conjSubgroup_eq_self_iff.mpr hmL
  have hne : ¬ conjSubgroup m B ≤ B ⊔ Z := by
    intro hle
    apply hmV
    have hle1 : (conjSubgroup m B ⊔ Z : Subgroup G) ≤ B ⊔ Z := sup_le hle le_sup_right
    have heq : (conjSubgroup m B ⊔ Z : Subgroup G) = B ⊔ Z :=
      Subgroup.eq_of_le_of_card_ge hle1 (by
        rw [hcA.card_sup_Z, hc.card_sup_Z, card_conjSubgroup])
    refine conjSubgroup_eq_self_iff.mp ?_
    rw [conjSubgroup_sup', hc.conj_Z_eq hm]
    exact heq
  have h1 := hc.card_LB_le_of_LB_eq hcA hLAB hne
  have h2 := hc.card_LB_ge hw (by omega : 1 ≤ n)
  have h3 : Nat.card Z ^ (n - 1) ≤ Nat.card Z :=
    Nat.le_of_mul_le_mul_left (h2.trans h1) Nat.card_pos
  have h4 := hc.hyp.q4
  have h5 : Nat.card Z ^ 2 ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

end CFSG.RankThree.GF2n.Stroth80
