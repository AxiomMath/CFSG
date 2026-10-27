module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S898

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem eq_seven_of_residual {n s r : ℕ} (hr : r.Prime) (hs : Odd s) (hsn : s ∣ n) (hrs : r ∣ 2 ^ s - 1)
    (hres : n = 3 ∨ n = 3 * r) : r = 7 := by
  suffices h : r ∣ 7 by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h with h | h
    · exact absurd h hr.ne_one
    · exact h
  rcases hres with rfl | rfl
  · rcases (Nat.dvd_prime Nat.prime_three).1 hsn with rfl | rfl
    · exact absurd (Nat.dvd_one.1 (by simpa using hrs)) hr.ne_one
    · simpa using hrs
  · obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.1 hsn
    rcases (Nat.dvd_prime Nat.prime_three).1 ha with ha1 | ha3 <;>
      rcases (Nat.dvd_prime hr).1 hb with hb1 | hbr
    · rw [ha1, hb1, mul_one] at hab
      rw [← hab] at hrs
      exact absurd (Nat.dvd_one.1 (by simpa using hrs)) hr.ne_one
    · rw [ha1, hbr, one_mul] at hab
      rw [← hab] at hrs
      exact absurd hrs (not_dvd_two_pow_sub_one_self hr)
    · rw [ha3, hb1, mul_one] at hab
      rw [← hab] at hrs
      simpa using hrs
    · rw [ha3, hbr] at hab
      rw [← hab] at hrs
      haveI : Fact r.Prime := ⟨hr⟩
      have h1 : ((2 ^ (3 * r) - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrs
      have h2 : (2 : ZMod r) ^ (3 * r) = 8 := by
        rw [pow_mul, ZMod.pow_card]
        norm_num
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, h2] at h1
      have h3 : ((7 : ℕ) : ZMod r) = 0 := by
        rw [Nat.cast_ofNat]
        linear_combination h1
      exact (ZMod.natCast_eq_zero_iff _ _).1 h3

theorem eq_bot_of_le_inf {Y : Type*} [Group Y] [Finite Y] {A A' E : Subgroup Y} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hsn : CFSG.Open.IsSubnormal A ⊤) (hp : ⁅A, A⁆ = A)
    (hqs : CFSG.Open.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) (hsn' : CFSG.Open.IsSubnormal A' ⊤)
    (hp' : ⁅A', A'⁆ = A') (hqs' : CFSG.Open.IsQuasisimple (↥A' ⧸ CFSG.pCore 2 ↥A')) (hne : A ≠ A')
    (hZ : ¬ q ∣ Nat.card (center (↥A ⧸ CFSG.pCore 2 ↥A))) (hEA : E ≤ A) (hEA' : E ≤ A')
    (hEel : IsElemAbelian q E) : E = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : Y →* Y ⧸ CFSG.pCore 2 Y := QuotientGroup.mk' (CFSG.pCore 2 Y)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hAc := isComponent_image hsn hqs
  have hA'c := isComponent_image hsn' hqs'
  have hne' : A.map π ≠ A'.map π := fun h => hne (image_injective hsn hp hsn' hp' h)
  have hcomm : ⁅A.map π, A'.map π⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hAc hA'c).resolve_left hne'
  have h1 : A.map π ≤ Subgroup.centralizer ((A'.map π : Subgroup _) : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hEπ : E.map π = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzA : z ∈ A.map π := Subgroup.map_mono hEA hz
    have hzA' : z ∈ A'.map π := Subgroup.map_mono hEA' hz
    have hzc : (⟨z, hzA⟩ : ↥(A.map π)) ∈ Subgroup.center ↥(A.map π) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 (h1 g.2) z hzA').symm
    have hzq : z ^ q = 1 := (hEel.map π).2 z hz
    have hcen : ¬ q ∣ Nat.card (Subgroup.center ↥(A.map π)) := by
      rw [← Nat.card_congr (Subgroup.centerCongr (barIso hsn)).toEquiv]
      exact hZ
    have hord1 : orderOf (⟨⟨z, hzA⟩, hzc⟩ : ↥(Subgroup.center ↥(A.map π))) ∣ q := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      apply Subtype.ext
      simpa using hzq
    have hord2 := orderOf_dvd_natCard (⟨⟨z, hzA⟩, hzc⟩ : ↥(Subgroup.center ↥(A.map π)))
    have hcop : Nat.Coprime q (Nat.card (Subgroup.center ↥(A.map π))) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 hcen
    have h1' : orderOf (⟨⟨z, hzA⟩, hzc⟩ : ↥(Subgroup.center ↥(A.map π))) ∣ Nat.gcd q
        (Nat.card (Subgroup.center ↥(A.map π))) := Nat.dvd_gcd hord1 hord2
    rw [hcop.gcd_eq_one] at h1'
    have h2 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1')
    have h3 : z = 1 := by
      have := congrArg (fun w : ↥(Subgroup.center ↥(A.map π)) =>
        ((w : ↥(A.map π)) : Y ⧸ CFSG.pCore 2 Y)) h2
      simpa using this
    rw [h3]
    exact Subgroup.one_mem _
  rw [eq_bot_iff]
  intro x hx
  have hπx : π x = 1 := by
    have : π x ∈ E.map π := ⟨x, hx, rfl⟩
    rw [hEπ] at this
    exact this
  have hxk : x ∈ π.ker := hπx
  exact Subgroup.mem_bot.2 (eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hEel.isPGroup hker hx hxk)

theorem mem_normalizer_of_centralizes {M L : Subgroup G} (hL : L ∈ calC M) {a : G} (ha : a ∈ M) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {X : Subgroup G} (hXL : X ≤ L) (hXc : Nat.card X = r)
    (hZ : ¬ r ∣ Nat.card (center (Bar2 L))) (hXa : ∀ x ∈ X, a * x * a⁻¹ = x) :
    a ∈ normalizer (L : Set G) := by
  classical
  by_contra hna
  let f : MulAut G := MulAut.conj a
  have hM : M.map f.toMonoidHom = M := mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer ha)
  have hL' : L.map f.toMonoidHom ∈ calC M := calC_map M f hM hL
  have hne : L ≠ L.map f.toMonoidHom := fun h => hna (mem_normalizer_iff_map_conj.2 h.symm)
  obtain ⟨hsn, hp, hqs, hcen⟩ := calC_subgroupOf hL
  obtain ⟨hsn', hp', hqs', hcen'⟩ := calC_subgroupOf hL'
  have hLM : L ≤ M := hL.1.le
  have hL'M : L.map f.toMonoidHom ≤ M := hL'.1.le
  have hne' : L.subgroupOf M ≠ (L.map f.toMonoidHom).subgroupOf M := by
    intro h
    apply hne
    have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hLM, Subgroup.map_subgroupOf_eq_of_le hL'M] at this
  have hXL' : X ≤ L.map f.toMonoidHom := fun x hx =>
    ⟨x, hXL hx, by simpa [f, MulAut.conj_apply] using hXa x hx⟩
  have hXM : X ≤ M := hXL.trans hLM
  have hbot := eq_bot_of_le_inf (A := L.subgroupOf M) (A' := (L.map f.toMonoidHom).subgroupOf M)
    (E := X.subgroupOf M) hr hr2 hsn hp hqs hsn' hp' hqs' hne' (by rw [hcen]; exact hZ)
    (fun x hx => hXL hx) (fun x hx => hXL' hx)
    ((isElemAbelian_of_card_prime hr hXc).subgroupOf M)
  have hX1 : X = ⊥ := by
    have := congrArg (Subgroup.map M.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hXM, Subgroup.map_bot] at this
  rw [hX1] at hXc
  simp at hXc
  exact hr.ne_one hXc.symm

theorem exists_lift_fixed {L B : Subgroup G} {ℓ q : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hBN : B ≤ normalizer (L : Set G)) (hB : IsPGroup ℓ B) (Eb : Subgroup (Bar2 L))
    (hEb : IsPGroup q Eb)
    (hfix : ∀ b (hb : b ∈ B), ∀ e ∈ Eb, rhoL L ⟨b, hBN hb⟩ e = e) :
    ∃ E : Subgroup G, E ≤ L ∧ E ≤ centralizer (B : Set G) ∧
      (E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤ Eb ∧ Nat.card E = Nat.card Eb ∧
      (IsElemAbelian q Eb → IsElemAbelian q E) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 Eb hEb
  let QG : Subgroup G := Q.map L.subtype
  have hQL : QG ≤ L := Subgroup.map_subtype_le _
  have hOL : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hQq : IsPGroup q QG := hQp.map _
  have hcomm : ∀ b ∈ B, ∀ a ∈ QG, b * a * b⁻¹ * a⁻¹ ∈ pCoreOf 2 L := by
    intro b hb a ha
    obtain ⟨a', ha'Q, rfl⟩ := ha
    have hmem : π a' ∈ Eb := by rw [← hQmap]; exact ⟨a', ha'Q, rfl⟩
    exact (rhoL_fix_iff L ⟨b, hBN hb⟩ a').1 (hfix b hb _ hmem)
  have hQN : QG ≤ normalizer (pCoreOf 2 L : Set G) :=
    hQL.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf L))
  have hBO : B ≤ normalizer (pCoreOf 2 L : Set G) := hBN.trans (normalizer_le_normalizer_pCoreOf L)
  obtain ⟨A', hA'c, hA'le, ⟨eqv⟩⟩ := exists_centralizing_copy hℓ hℓ2 hq hq2 (pCoreOf 2 L) QG B
    (isPGroup_pCoreOf L) hQN hBO hQq hB hcomm
  have hA'L : A' ≤ L := hA'le.trans (sup_le hQL hOL)
  refine ⟨A', hA'L, hA'c, ?_, ?_, ?_⟩
  ·
    have hle : QG ⊔ pCoreOf 2 L ≤ (Eb.comap π).map L.subtype := by
      refine sup_le ?_ ?_
      · rintro _ ⟨a', ha'Q, rfl⟩
        exact ⟨a', by
          show π a' ∈ Eb
          rw [← hQmap]; exact ⟨a', ha'Q, rfl⟩, rfl⟩
      · rintro _ ⟨o', ho', rfl⟩
        refine ⟨o', ?_, rfl⟩
        show π o' ∈ Eb
        have : π o' = 1 := (QuotientGroup.eq_one_iff o').2 ho'
        rw [this]
        exact Eb.one_mem
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x', hx', hxw⟩ := hle (hA'le hw)
    have : x' = w := Subtype.ext hxw
    rw [← this]
    exact hx'
  · rw [Nat.card_congr eqv.toEquiv, Subgroup.card_map_of_injective L.subtype_injective,
      ← card_map_of_disjoint_ker π Q hQdisj, hQmap]
  · intro hEel
    have h1 : IsElemAbelian q Q := isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hEel)
    exact isElemAbelian_of_mulEquiv eqv (h1.map _)

theorem exists_pgroup_containing {L : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (Eb : Subgroup (Bar2 L)) (hEb : IsPGroup q Eb) {A : Subgroup G} (hAL : A ≤ L) (hAq : IsPGroup q A)
    (hAE : (A.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤ Eb) :
    ∃ S : Subgroup G, S ≤ L ∧ A ≤ S ∧ Nat.card S = Nat.card Eb ∧
      (IsElemAbelian q Eb → IsElemAbelian q S) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  let H : Subgroup ↥L := Eb.comap π
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 Eb hEb
  have hQH : Q ≤ H := fun x hx => by
    show π x ∈ Eb
    rw [← hQmap]; exact ⟨x, hx, rfl⟩
  let A' : Subgroup ↥L := A.subgroupOf L
  have hA'H : A' ≤ H := fun x hx => hAE ⟨x, hx, rfl⟩
  have hA'q : IsPGroup q A' := hAq.comap_subtype
  have hQ'p : IsPGroup q (Q.subgroupOf H) := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hA''p : IsPGroup q (A'.subgroupOf H) := hA'q.of_equiv (Subgroup.subgroupOfEquivOfLe hA'H).symm
  obtain ⟨S₁, hS₁⟩ := hQ'p.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := hA''p.exists_le_sylow
  have hcard12 : Nat.card S₂ = Nat.card S₁ := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  let T₂ : Subgroup ↥L := (S₂ : Subgroup ↥H).map H.subtype
  have hT₂H : T₂ ≤ H := Subgroup.map_subtype_le _
  have hT₂p : IsPGroup q T₂ := S₂.isPGroup'.map _
  have hT₂disj : Disjoint T₂ π.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxk
    exact eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hT₂p hker hxT hxk
  have hT₂card : Nat.card T₂ = Nat.card S₂ :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hle1 : Nat.card T₂ ≤ Nat.card Eb := by
    have h1 : T₂.map π ≤ Eb := by
      rintro _ ⟨x, hx, rfl⟩
      exact hT₂H hx
    calc Nat.card T₂ = Nat.card (T₂.map π) := (card_map_of_disjoint_ker π T₂ hT₂disj).symm
      _ ≤ Nat.card Eb := Subgroup.card_le_of_le h1
  have hle2 : Nat.card Eb ≤ Nat.card S₁ := by
    have h1 : Nat.card Q ≤ Nat.card S₁ := by
      calc Nat.card Q = Nat.card (Q.subgroupOf H) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv.symm
        _ ≤ Nat.card S₁ := Subgroup.card_le_of_le hS₁
    rw [← hQmap, card_map_of_disjoint_ker π Q hQdisj]
    exact h1
  have hcard : Nat.card T₂ = Nat.card Eb := by
    apply le_antisymm hle1
    calc Nat.card Eb ≤ Nat.card S₁ := hle2
      _ = Nat.card S₂ := hcard12.symm
      _ = Nat.card T₂ := hT₂card.symm
  refine ⟨T₂.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro a ha
    have hx : (⟨a, hAL ha⟩ : ↥L) ∈ A' := ha
    have hx' : (⟨⟨a, hAL ha⟩, hA'H hx⟩ : ↥H) ∈ A'.subgroupOf H := hx
    exact ⟨⟨a, hAL ha⟩, ⟨_, hS₂ hx', rfl⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]
  · intro hEel
    have h1 : T₂.map π ≤ Eb := by
      rintro _ ⟨x, hx, rfl⟩
      exact hT₂H hx
    exact (isElemAbelian_of_disjoint_ker π T₂ hT₂disj (hEel.mono h1)).map _

theorem normalizer_le_gamma {E A : Subgroup G} (hAE : A ≤ E) {p : ℕ} (hp : p.Prime)
    (hA : IsElemAbelian p A) (hcard : Nat.card A = p) : normalizer (A : Set G) ≤ rankThreeGamma 1 p E := by
  unfold rankThreeGamma GLBCore
  exact le_sSup ⟨A, hAE, le_pRank' hp (le_refl A) hA (by rw [pow_one]; exact hcard), rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6S898
