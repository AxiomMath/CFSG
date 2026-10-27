module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 (calNIn CFShape)

@[expose] def onl_SecL3 (G : Type) [Group G] : Prop :=
  ∀ (Λ : Type) [Group Λ], uc22p20bSimpSec G Λ → (∃ a b : Λ, a * b ≠ b * a) → IsL3 Λ 2

theorem onl_cfShape_of_secL3 {G : Type} [Group G] (h : onl_SecL3 G) :
    CFShape G (fun X _ => IsL3 X 2) :=
  fun L _ hL hnc => h L (uc22p20b_simpSec_of_cf hL) hnc

theorem onl_secL3_of_surjective {A Q : Type} [Group A] [Group Q] (ψ : Q →* A)
    (hψ : Function.Surjective ψ) (h : onl_SecL3 Q) : onl_SecL3 A :=
  fun Λ _ hs hnc => h Λ (uc22p20b_simpSec_of_surjective ψ hψ hs) hnc

theorem onl_secL3_of_normal {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] (h : onl_SecL3 ↥N) : onl_SecL3 G := by
  intro Λ _ hs hnc
  rcases uc22p20b_simpSec_restrict N hs with h1 | h1
  · exact h Λ h1 hnc
  · obtain ⟨a, b, hab⟩ := hnc
    exact absurd (uc22p20b_simpSec_comm h1 a b) hab

theorem onl_secL3_of_normal' {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsSolvable ↥N] (h : onl_SecL3 (G ⧸ N)) : onl_SecL3 G := by
  intro Λ _ hs hnc
  rcases uc22p20b_simpSec_restrict N hs with h1 | h1
  · obtain ⟨a, b, hab⟩ := hnc
    exact absurd (uc22p20b_simpSec_comm h1 a b) hab
  · exact h Λ h1 hnc

theorem onl_calNIn_of_prime {G : Type} [Group G] {S H : Subgroup G} (hSH : S ≤ H) {p : ℕ}
    (hp : p.Prime) (hidx : S.relIndex H = p) : calNIn H S = {S} := by
  have key : ∀ X : Subgroup G, S ≤ X → X ≤ H → X = S ∨ X = H := by
    intro X hSX hXH
    have h1 := Subgroup.relIndex_mul_relIndex S X H hSX hXH
    rw [hidx] at h1
    rcases (Nat.dvd_prime hp).1 (Dvd.intro _ h1) with h | h
    · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h) hSX)
    · right
      rw [h] at h1
      have h2 : X.relIndex H = 1 := by
        have := hp.pos
        nlinarith
      exact le_antisymm hXH (Subgroup.relIndex_eq_one.1 h2)
  have hne : S ≠ H := by
    rintro rfl
    rw [Subgroup.relIndex_self] at hidx
    exact hp.one_lt.ne hidx
  ext X
  simp only [calNIn, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hSX, hXH, -⟩
    rcases key X hSX hXH.le with h | h
    · exact h
    · exact absurd h hXH.ne
  · rintro rfl
    refine ⟨le_rfl, lt_of_le_of_ne hSH hne, fun Y hSY hYH => ?_⟩
    rcases key Y hSY.le hYH with h | h
    · exact absurd h hSY.ne'
    · exact h

theorem onl_calNIn_of_chain {G : Type} [Group G] {S M H : Subgroup G} (hSM : S ≤ M)
    (hMH : M ≤ H) (hSM' : S ≠ M) (hMH' : M ≠ H)
    (hch : ∀ X : Subgroup G, S ≤ X → X ≤ H → X = S ∨ X = M ∨ X = H) : calNIn H S = {M} := by
  ext X
  simp only [calNIn, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hSX, hXH, hmax⟩
    rcases hch X hSX hXH.le with rfl | rfl | rfl
    · exact absurd (hmax M (lt_of_le_of_ne hSM hSM') hMH) hMH'
    · rfl
    · exact absurd rfl hXH.ne
  · rintro rfl
    refine ⟨hSM, lt_of_le_of_ne hMH hMH', fun Y hXY hYH => ?_⟩
    rcases hch Y (hSM.trans hXY.le) hYH with rfl | rfl | rfl
    · exact absurd (lt_of_le_of_lt hSM hXY) (lt_irrefl _)
    · exact absurd rfl hXY.ne
    · rfl

theorem onl_isSolvable_of_card {G : Type} [Group G] [Finite G] {a : ℕ}
    (h : Nat.card G = 2 ^ a * 3) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := a) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h, pow_one])

@[expose] def onl_Concl (Y : Type) [Group Y] (S : Subgroup Y) : Prop :=
  ∃ H₁ H₂ M₁ M₂ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ H₁ ⊔ H₂ = ⊤ ∧
    3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂ ∧
    calNIn H₁ S = {M₁} ∧ Group.IsSolvable ↥H₁ ∧
    calNIn H₂ S = {M₂} ∧ onl_SecL3 ↥H₂

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem onl_concl_of_model {Γ : Type} [Group Γ] [Finite Γ] {U B C P : Subgroup Γ}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUB : U < B) (hBC : B < C) (hUP : U ≤ P)
    (hlat : ∀ X : Subgroup Γ, U ≤ X → X ≤ C → X = U ∨ X = B ∨ X = C)
    (h3C : 3 ∣ Nat.card C) (hP : Nat.card P = 3 * Nat.card U) (hgen : P ⊔ C = ⊤)
    (hsec : onl_SecL3 ↥C)
    (hinvC : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → C.map α.toMonoidHom = C)
    (hinvB : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → B.map α.toMonoidHom = B)
    (hinvP : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P)
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [hK : K.Normal]
    (hidx : ∃ a : ℕ, K.index = 2 ^ a) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (e : ↥K ≃* Γ) : onl_Concl Y S := by
  classical
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK hU
  set pl : Subgroup Γ → Subgroup Y := fun X => (X.map e'.symm.toMonoidHom).map K.subtype
    with hpl
  have hα : ∀ t ∈ S, U.map (autK e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (SporB.le_normalizer_inf hK ht)
  have hnorm : ∀ X : Subgroup Γ,
      (∀ α : MulAut Γ, U.map α.toMonoidHom = U → X.map α.toMonoidHom = X) →
      S ≤ Subgroup.normalizer (pl X : Set Y) := fun X hX t ht =>
    mem_normalizer_pull e' (hX _ (hα t ht))
  have hSKle : ∀ X : Subgroup Γ, U ≤ X → S ⊓ K ≤ pl X := fun X hUX =>
    (le_pull_iff e' inf_le_right).mpr (he' ▸ hUX)
  have hcardSK : Nat.card ↥(S ⊓ K) = Nat.card U := by
    rw [← he', Subgroup.card_map_of_injective e'.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have hcardpl : ∀ X : Subgroup Γ, Nat.card (pl X) = Nat.card X := fun X => by
    simp only [hpl]
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e'.symm.injective]
  have hplK : ∀ X : Subgroup Γ, pl X ≤ K := fun X => pull_le e' X
  have hinf : ∀ X : Subgroup Γ, U ≤ X → S ⊓ pl X = S ⊓ K := fun X hUX =>
    le_antisymm (inf_le_inf_left _ (hplK X)) (le_inf inf_le_left (hSKle X hUX))
  have hcardsup : ∀ X : Subgroup Γ, U ≤ X →
      (∀ α : MulAut Γ, U.map α.toMonoidHom = U → X.map α.toMonoidHom = X) →
      Nat.card ↥(S ⊔ pl X) * Nat.card U = Nat.card S * Nat.card X := fun X hUX hX => by
    have h :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (hnorm X hX)
    rw [hinf X hUX, hcardSK, hcardpl] at h
    exact h
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have hS0 : 0 < Nat.card S := Nat.card_pos
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  obtain ⟨j, hj⟩ := hU.2.1.exists_card_eq
  have hUC : U ≤ C := hUB.le.trans hBC.le
  have hplU : pl U = S ⊓ K :=
    (Subgroup.eq_of_le_of_card_ge (hSKle U le_rfl) (by rw [hcardpl, hcardSK])).symm
  have hc1 : Nat.card ↥(S ⊔ pl P) = 3 * Nat.card S := by
    have h := hcardsup P hUP hinvP
    rw [hP] at h
    have h2 : Nat.card ↥(S ⊔ pl P) * Nat.card U = (3 * Nat.card S) * Nat.card U := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hU0 h2
  have hcB := hcardsup B hUB.le hinvB
  have hcC := hcardsup C hUC hinvC
  have hltUB : Nat.card U < Nat.card B := Subgroup.card_lt_of_lt hUB
  have hltBC : Nat.card B < Nat.card C := Subgroup.card_lt_of_lt hBC
  have hKS : K ⊔ S = ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hidx' : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
    exact CFSG.QuasiDihedralFusion.normal_sup_sylow_eq_top K hidx (hS.2.1.toSylow hidx')
  have hnC := hnorm C hinvC
  have hchain : ∀ X : Subgroup Y, S ≤ X → X ≤ S ⊔ pl C →
      X = S ∨ X = S ⊔ pl B ∨ X = S ⊔ pl C := by
    intro X hSX hXH
    set X₀ := X ⊓ pl C with hX₀
    have hX₀K : X₀ ≤ K := inf_le_right.trans (hplK C)
    have hXeq : X = S ⊔ X₀ := by
      refine le_antisymm (fun x hx => ?_) (sup_le hSX inf_le_left)
      have hx' : x ∈ pl C ⊔ S := by rw [sup_comm]; exact hXH hx
      obtain ⟨n, hn, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hnC hx'
      have hnX : n ∈ X := by
        have := X.mul_mem hx (X.inv_mem (hSX hs))
        simpa using this
      rw [sup_comm]
      exact Subgroup.mul_mem_sup ⟨hnX, hn⟩ hs
    set X₁ := (X₀.subgroupOf K).map e'.toMonoidHom with hX₁
    have hUX₁ : U ≤ X₁ := by
      rw [← he', hX₁]
      refine Subgroup.map_mono fun y hy => ?_
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact ⟨hSX hy.1, hSKle C hUC hy⟩
    have hX₁C : X₁ ≤ C := (le_pull_iff e' hX₀K).mp inf_le_right
    have hX₀pl : X₀ = pl X₁ := (pull_map e' hX₀K).symm
    rcases hlat X₁ hUX₁ hX₁C with h | h | h
    · left
      rw [hXeq, hX₀pl, h, hplU]
      exact sup_eq_left.2 inf_le_left
    · right; left
      rw [hXeq, hX₀pl, h]
    · right; right
      rw [hXeq, hX₀pl, h]
  have hH₂N : S ⊔ pl C ≤ Subgroup.normalizer (pl C : Set Y) :=
    sup_le hnC Subgroup.le_normalizer
  have hplCH₂ : pl C ≤ S ⊔ pl C := le_sup_right
  have hNn : ((pl C).subgroupOf (S ⊔ pl C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hplCH₂).mpr hH₂N
  have hsolvq : Group.IsSolvable (↥(S ⊔ pl C) ⧸ (pl C).subgroupOf (S ⊔ pl C)) := by
    have hSH₂ : S ≤ S ⊔ pl C := le_sup_left
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' ((pl C).subgroupOf (S ⊔ pl C))).comp (Subgroup.inclusion hSH₂)) := by
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
      have hx' : x ∈ pl C ⊔ S := by rw [sup_comm]; exact hx
      obtain ⟨n, hn, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hnC hx'
      refine ⟨⟨s, hs⟩, ?_⟩
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 := (Subgroup.mem_normalizer_iff.mp (hnC (S.inv_mem hs)) n).mp hn
      simpa [mul_assoc] using h1
    have : Group.IsSolvable ↥S := by
      have := hS.2.1.isNilpotent
      infer_instance
    exact Group.isSolvable_of_surjective hsurj
  have hsecH₂ : onl_SecL3 ↥(S ⊔ pl C) := by
    have := hsolvq
    refine onl_secL3_of_normal ((pl C).subgroupOf (S ⊔ pl C)) ?_
    let ψ : ↥C ≃* ↥((pl C).subgroupOf (S ⊔ pl C)) :=
      ((C.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective).trans
        ((C.map e'.symm.toMonoidHom).equivMapOfInjective K.subtype K.subtype_injective)).trans
        (Subgroup.subgroupOfEquivOfLe hplCH₂).symm
    exact onl_secL3_of_surjective ψ.toMonoidHom ψ.surjective hsec
  refine ⟨S ⊔ pl P, S ⊔ pl C, S, S ⊔ pl B, le_sup_left, le_sup_left, ?_, ?_, ?_, ?_, ?_, ?_,
    hsecH₂⟩
  ·
    have hgK : pl P ⊔ pl C = K := by rw [← pull_sup, hgen, pull_top]
    rw [eq_top_iff, ← hKS]
    refine sup_le ?_ (le_sup_left.trans le_sup_left)
    rw [← hgK]
    exact sup_le_sup le_sup_right le_sup_right
  · rw [hc1]; exact dvd_mul_right 3 _
  · have h3 : 3 ∣ Nat.card ↥(S ⊔ pl C) * Nat.card U := by
      rw [hcC]; exact dvd_mul_of_dvd_right h3C _
    have hcop : Nat.Coprime 3 (Nat.card U) := by
      rw [hj]; exact Nat.Coprime.pow_right _ (by norm_num)
    exact hcop.dvd_of_dvd_mul_right h3
  · refine onl_calNIn_of_prime le_sup_left Nat.prime_three ?_
    have h1 := Subgroup.relIndex_mul_card (H := S) (K := S ⊔ pl P)
    rw [inf_of_le_left le_sup_left, hc1] at h1
    exact Nat.eq_of_mul_eq_mul_right hS0 h1
  · rw [hk] at hc1
    rw [show 3 * 2 ^ k = 2 ^ k * 3 by ring] at hc1
    exact onl_isSolvable_of_card hc1
  · refine onl_calNIn_of_chain le_sup_left (sup_le_sup_left (pull_mono e' hBC.le) _) ?_ ?_
      hchain
    · intro h
      have h2 : Nat.card ↥(S ⊔ pl B) * Nat.card U = Nat.card S * Nat.card U := by
        rw [← h]
      rw [hcB] at h2
      have := Nat.eq_of_mul_eq_mul_left hS0 h2
      omega
    · intro h
      have h2 := hcC
      rw [← h, hcB] at h2
      have := Nat.eq_of_mul_eq_mul_left hS0 h2
      omega

theorem onl_lift_one {Y : Type} [Group Y] [Finite Y] {Z S : Subgroup Y} [Z.Normal]
    (hZ3 : Nat.card Z = 3) {Hb Mb : Subgroup (Y ⧸ Z)}
    (hSH : S.map (QuotientGroup.mk' Z) ≤ Hb)
    (hcal : calNIn Hb (S.map (QuotientGroup.mk' Z)) = {Mb}) :
    ∃ H M : Subgroup Y, S ≤ H ∧ H.map (QuotientGroup.mk' Z) = Hb ∧ calNIn H S = {M} ∧
      (H ⊓ Z = ⊥ ∨ Z ≤ H) := by
  classical
  set π := QuotientGroup.mk' Z with hπ
  set Hh := Hb.comap π with hHh
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hSHh : S ≤ Hh := Subgroup.map_le_iff_le_comap.mp hSH
  have hZHh : Z ≤ Hh := hker ▸ Subgroup.ker_le_comap π Hb
  have hmapHh : Hh.map π = Hb := Subgroup.map_comap_eq_self_of_surjective hsurj Hb
  have hMb : Mb ∈ calNIn Hb (S.map π) := by rw [hcal]; rfl
  by_cases hc : ∃ X : Subgroup Y, S ≤ X ∧ X ≤ Hh ∧ X ⊓ Z = ⊥ ∧ X ⊔ Z = Hh
  · obtain ⟨X, hSX, -, hXZ, hXZH⟩ := hc
    have hZb : Z.map π = ⊥ := by rw [Subgroup.map_eq_bot_iff, hker]
    have hXmap : X.map π = Hb := by
      rw [← hmapHh, ← hXZH, Subgroup.map_sup, hZb, sup_bot_eq]
    have c1 : ∀ W : Subgroup Y, W ≤ X → X ⊓ (W.map π).comap π = W := by
      intro W hWX
      refine le_antisymm (fun x hx => ?_) (le_inf hWX (Subgroup.le_comap_map π W))
      obtain ⟨hxX, w, hw, hwx⟩ := hx
      have hz : w⁻¹ * x ∈ Z := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hwx, inv_mul_cancel]
      have hzX : w⁻¹ * x ∈ X := X.mul_mem (X.inv_mem (hWX hw)) hxX
      have h1 : w⁻¹ * x ∈ X ⊓ Z := ⟨hzX, hz⟩
      rw [hXZ, Subgroup.mem_bot] at h1
      have : x = w := by
        calc x = w * (w⁻¹ * x) := by group
          _ = w := by rw [h1, mul_one]
      rw [this]; exact hw
    have c2 : ∀ W : Subgroup (Y ⧸ Z), W ≤ Hb → (X ⊓ W.comap π).map π = W := by
      intro W hWH
      refine le_antisymm ((Subgroup.map_mono inf_le_right).trans
        (Subgroup.map_comap_le π W)) (fun w hw => ?_)
      obtain ⟨x, hxX, rfl⟩ := (hXmap ▸ hWH hw : w ∈ X.map π)
      exact ⟨x, ⟨hxX, hw⟩, rfl⟩
    refine ⟨X, X ⊓ Mb.comap π, hSX, hXmap, ?_, Or.inl hXZ⟩
    ext W
    simp only [calNIn, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hSW, hWX, hmax⟩
      have hW : W.map π ∈ calNIn Hb (S.map π) := by
        refine ⟨Subgroup.map_mono hSW, lt_of_le_of_ne (hXmap ▸ Subgroup.map_mono hWX.le) ?_,
          fun V hWV hVH => ?_⟩
        · intro h
          apply hWX.ne
          rw [← c1 W hWX.le, h, ← hXmap, c1 X le_rfl]
        · have hle : W ≤ X ⊓ V.comap π :=
            le_inf hWX.le (Subgroup.map_le_iff_le_comap.mp hWV.le)
          have hne : W ≠ X ⊓ V.comap π := by
            intro h
            apply hWV.ne
            rw [h, c2 V hVH]
          have := hmax _ (lt_of_le_of_ne hle hne) inf_le_left
          rw [← c2 V hVH, this, hXmap]
      rw [hcal] at hW
      have hW' : W.map π = Mb := hW
      rw [← c1 W hWX.le, hW']
    · rintro rfl
      obtain ⟨hSMb, hMbH, hmaxb⟩ := hMb
      refine ⟨le_inf hSX (Subgroup.map_le_iff_le_comap.mp hSMb),
        lt_of_le_of_ne inf_le_left ?_, fun V hWV hVX => ?_⟩
      · intro h
        apply hMbH.ne
        rw [← c2 Mb hMbH.le, h, hXmap]
      · have h1 : Mb ≤ V.map π := by
          rw [← c2 Mb hMbH.le]; exact Subgroup.map_mono hWV.le
        have h2 : V.map π ≤ Hb := hXmap ▸ Subgroup.map_mono hVX
        have h3 : Mb ≠ V.map π := by
          intro h
          apply hWV.ne
          rw [h, c1 V hVX]
        have := hmaxb _ (lt_of_le_of_ne h1 h3) h2
        rw [← c1 V hVX, this, ← hXmap, c1 X le_rfl]
  · have hZW : ∀ W : Subgroup Y, W ∈ calNIn Hh S → Z ≤ W := by
      rintro W ⟨hSW, hWH, hmax⟩
      by_contra hZW
      have hWZ : W ⊓ Z = ⊥ := by
        have hd : Nat.card ↥(W ⊓ Z) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
        · exact Subgroup.eq_bot_of_card_eq _ h
        · exfalso
          apply hZW
          have : W ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hZ3])
          rw [← this]
          exact inf_le_left
      have hlt : W < W ⊔ Z := lt_of_le_of_ne le_sup_left (fun h => hZW (h ▸ le_sup_right))
      exact hc ⟨W, hSW, hWH.le, hWZ, hmax _ hlt (sup_le hWH.le hZHh)⟩
    have d1 : ∀ W : Subgroup Y, Z ≤ W → (W.map π).comap π = W := fun W hZW => by
      rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hZW]
    have d2 : ∀ W : Subgroup (Y ⧸ Z), (W.comap π).map π = W := fun W =>
      Subgroup.map_comap_eq_self_of_surjective hsurj W
    refine ⟨Hh, Mb.comap π, hSHh, hmapHh, ?_, Or.inr hZHh⟩
    ext W
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hW
      have hZ := hZW W hW
      obtain ⟨hSW, hWH, hmax⟩ := hW
      have hWb : W.map π ∈ calNIn Hb (S.map π) := by
        refine ⟨Subgroup.map_mono hSW, lt_of_le_of_ne (hmapHh ▸ Subgroup.map_mono hWH.le) ?_,
          fun V hWV hVH => ?_⟩
        · intro h
          apply hWH.ne
          rw [← d1 W hZ, h]
        · have hle : W ≤ V.comap π := by rw [← d1 W hZ]; exact Subgroup.comap_mono hWV.le
          have hne : W ≠ V.comap π := by intro h; apply hWV.ne; rw [h, d2]
          have := hmax _ (lt_of_le_of_ne hle hne) (Subgroup.comap_mono hVH)
          rw [← d2 V, this, hmapHh]
      rw [hcal] at hWb
      have : W.map π = Mb := hWb
      rw [← d1 W hZ, this]
    · rintro rfl
      obtain ⟨hSMb, hMbH, hmaxb⟩ := hMb
      refine ⟨Subgroup.map_le_iff_le_comap.mp hSMb,
        lt_of_le_of_ne (Subgroup.comap_mono hMbH.le) ?_, fun V hWV hVH => ?_⟩
      · intro h
        apply hMbH.ne
        rw [← d2 Mb, h, hmapHh]
      · have hZV : Z ≤ V := (hker ▸ Subgroup.ker_le_comap π Mb).trans hWV.le
        have h1 : Mb ≤ V.map π := by rw [← d2 Mb]; exact Subgroup.map_mono hWV.le
        have h3 : Mb ≠ V.map π := by intro h; apply hWV.ne; rw [h, d1 V hZV]
        have := hmaxb _ (lt_of_le_of_ne h1 h3) (hmapHh ▸ Subgroup.map_mono hVH)
        rw [← d1 V hZV, this]

theorem onl_lift_props {Y : Type} [Group Y] [Finite Y] {Z : Subgroup Y} [Z.Normal]
    (hZ3 : Nat.card Z = 3) {H : Subgroup Y} {Hb : Subgroup (Y ⧸ Z)}
    (hm : H.map (QuotientGroup.mk' Z) = Hb) (hd : H ⊓ Z = ⊥ ∨ Z ≤ H) :
    (3 ∣ Nat.card Hb → 3 ∣ Nat.card H) ∧ (Group.IsSolvable Hb → Group.IsSolvable H) ∧
      (onl_SecL3 Hb → onl_SecL3 H) := by
  set φ : ↥H →* Y ⧸ Z := (QuotientGroup.mk' Z).comp H.subtype with hφ
  have hrange : φ.range = Hb := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]; exact hm
  have hker : φ.ker = Z.subgroupOf H := by
    ext x
    simp [hφ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  rcases hd with hd | hd
  · have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, hker, eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have h1 : (x : Y) ∈ H ⊓ Z := ⟨x.2, hx⟩
      rw [hd, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.2 (Subtype.ext h1)
    let ι : ↥H ≃* ↥Hb := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    refine ⟨fun h3 => ?_, fun hs => ?_, fun hsec => ?_⟩
    · rw [Nat.card_congr ι.toEquiv]; exact h3
    · exact Group.isSolvable_of_surjective (f := ι.symm.toMonoidHom) ι.symm.surjective
    · exact onl_secL3_of_surjective ι.symm.toMonoidHom ι.symm.surjective hsec
  · let ι : (↥H ⧸ Z.subgroupOf H) ≃* ↥Hb :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
    have hZc : Nat.card ↥(Z.subgroupOf H) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd).toEquiv, hZ3]
    have : Group.IsSolvable ↥(Z.subgroupOf H) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have := (IsPGroup.of_card (p := 3) (n := 1) (by rw [hZc, pow_one])).isNilpotent
      infer_instance
    refine ⟨fun _ => ?_, fun hs => ?_, fun hsec => ?_⟩
    · rw [← hZ3]; exact Subgroup.card_dvd_of_le hd
    · have := hs
      have : Group.IsSolvable (↥H ⧸ Z.subgroupOf H) :=
        Group.isSolvable_of_surjective (f := ι.symm.toMonoidHom) ι.symm.surjective
      exact Group.isSolvable_of_subgroup_quotient (Z.subgroupOf H)
    · exact onl_secL3_of_normal' (Z.subgroupOf H)
        (onl_secL3_of_surjective ι.symm.toMonoidHom ι.symm.surjective hsec)

theorem onl_concl_of_quot {Y : Type} [Group Y] [Finite Y] {K S Z : Subgroup Y} [Z.Normal]
    (hZK : Z ≤ K) (hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z) (hperf : K ≤ ⁅K, K⁆)
    (hZ3 : Nat.card Z = 3) (h : onl_Concl (Y ⧸ Z) (S.map (QuotientGroup.mk' Z))) :
    onl_Concl Y S := by
  obtain ⟨Hb₁, Hb₂, Mb₁, Mb₂, hS₁, hS₂, hgen, h3₁, h3₂, hc₁, hsol, hc₂, hsec⟩ := h
  obtain ⟨H₁, M₁, hSH₁, hm₁, hcal₁, hd₁⟩ := onl_lift_one hZ3 hS₁ hc₁
  obtain ⟨H₂, M₂, hSH₂, hm₂, hcal₂, hd₂⟩ := onl_lift_one hZ3 hS₂ hc₂
  obtain ⟨p3₁, ps₁, -⟩ := onl_lift_props hZ3 hm₁ hd₁
  obtain ⟨p3₂, -, pc₂⟩ := onl_lift_props hZ3 hm₂ hd₂
  refine ⟨H₁, H₂, M₁, M₂, hSH₁, hSH₂, ?_, p3₁ h3₁, p3₂ h3₂, hcal₁, ps₁ hsol, hcal₂, pc₂ hsec⟩
  apply eq_top_of_sup_eq_top_of_central hZK hZc hperf
  have h1 : (H₁ ⊔ H₂).map (QuotientGroup.mk' Z) = ⊤ := by rw [Subgroup.map_sup, hm₁, hm₂, hgen]
  have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' Z)) h1
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
