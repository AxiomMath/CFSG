module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofPair
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG.ComponentClassification

private theorem exists_hom_ker_eq_right {Q : Type*} [Group Q] [Finite Q] {U V : Subgroup Q}
    (hP : Sec14.Res9Pair.IsPair U V) :
    ∃ π : Q →* alternatingGroup (Fin 6), π.ker = V := by
  have := hP.normal_left
  have := hP.normal_right
  obtain ⟨-, ⟨e⟩⟩ := hP.cover_left
  let φ : ↥U →* Q ⧸ V := (QuotientGroup.mk' V).comp U.subtype
  have hker : φ.ker = Subgroup.center ↥U := by
    ext u
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' V (u : Q) = 1 ↔ u ∈ Subgroup.center ↥U
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h1 : (u : Q) ∈ V ↔ (u : Q) ∈ U ⊓ V := ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
    rw [h1, hP.inf_eq]
    constructor
    · intro h
      obtain ⟨_, h'⟩ := Sec14.Item148PtRes.mem_centerIn_iff.mp h
      exact h'
    · intro h
      exact Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨u.2, h⟩
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V x
    obtain ⟨y, hy, v, hv, rfl⟩ := Sec14.Item148PtRes.exists_mul_eq hP.sup_eq g
    refine ⟨⟨y, hy⟩, ?_⟩
    change QuotientGroup.mk' V y = QuotientGroup.mk' V (y * v)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using hv
  let χ : Q ⧸ V ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans e
  refine ⟨χ.toMonoidHom.comp (QuotientGroup.mk' V), ?_⟩
  ext x
  rw [MonoidHom.mem_ker]
  change χ (QuotientGroup.mk' V x) = 1 ↔ x ∈ V
  rw [χ.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

private theorem normal_le_center_or_eq_top_of_quasisimple {K : Type*} [Group K]
    (hK : CFSG.IsQuasisimple K) {N : Subgroup K} [N.Normal] :
    N ≤ Subgroup.center K ∨ N = ⊤ := by
  obtain ⟨hperf, hsimp, -⟩ := hK
  have hP : (N.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center K))) with hb | ht
  · left
    intro x hx
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center K)) hx
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · right
    have hdec : ∀ x : K, ∃ n ∈ N, ∃ z ∈ Subgroup.center K, x = n * z := by
      intro x
      have h1 : QuotientGroup.mk' (Subgroup.center K) x ∈
          N.map (QuotientGroup.mk' (Subgroup.center K)) := by
        rw [ht]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnx
      exact ⟨n, hn, n⁻¹ * x, hnx, by group⟩
    have hle : ⁅(⊤ : Subgroup K), ⊤⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec g₁
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec g₂
      rw [Sec14.Item148HJ.commutatorElement_mul_central hz₁ hz₂]
      exact Subgroup.commutator_le_self N (Subgroup.commutator_mem_commutator hn₁ hn₂)
    have htop : ⁅(⊤ : Subgroup K), ⊤⁆ = ⊤ :=
      (commutator_def K).symm.trans Group.IsPerfect.commutator_eq_top
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ := by
      rw [htop]
      exact Subgroup.mem_top x
    exact hle hx

private theorem forall_exists_mem_eq_of_card {Q : Type*} [Group Q] {K : Subgroup Q}
    (hK : Nat.card ↥K = 1080) (π : Q →* alternatingGroup (Fin 6))
    (hN : Nat.card ↥(π.ker.subgroupOf K) ≤ 3) :
    ∀ a : alternatingGroup (Fin 6), ∃ k ∈ K, π k = a := by
  set ψ : ↥K →* alternatingGroup (Fin 6) := π.comp K.subtype with hψ
  have hker : ψ.ker = π.ker.subgroupOf K := by
    ext x
    simp [hψ, Subgroup.mem_subgroupOf]
  have h1 : Nat.card ψ.ker * Nat.card ψ.range = 1080 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hK]
  have hkerN : Nat.card ψ.ker ≤ 3 := by
    rw [hker]
    exact hN
  have h2 : 1080 ≤ 3 * Nat.card ψ.range := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ hkerN
  have h4 : Nat.card ψ.range ≤ 360 := by
    rw [← Sec14.Item148HJ.card_alternatingGroup_six]
    exact Subgroup.card_le_card_group _
  have h5 : Nat.card ψ.range = Nat.card (alternatingGroup (Fin 6)) := by
    rw [Sec14.Item148HJ.card_alternatingGroup_six]
    omega
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ h5
  intro a
  have ha : a ∈ ψ.range := by
    rw [htop]
    exact Subgroup.mem_top a
  obtain ⟨k, hk⟩ := ha
  exact ⟨(k : Q), k.2, hk⟩

private theorem mem_ker_of_centralizes {Q : Type*} [Group Q] {K : Subgroup Q} {w : Q}
    (π : Q →* alternatingGroup (Fin 6))
    (hsurj : ∀ a : alternatingGroup (Fin 6), ∃ k ∈ K, π k = a)
    (hw : ∀ k ∈ K, k * w = w * k) : w ∈ π.ker := by
  have hcen : π w ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨k, hk, rfl⟩ := hsurj a
    rw [← map_mul, ← map_mul, hw k hk]
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen
  exact MonoidHom.mem_ker.mpr hcen

private theorem eq_bot_of_isPGroup_le_of_card_eq_three {Q : Type*} [Group Q] {X W : Subgroup Q}
    (hW : IsPGroup 2 W) (hX : Nat.card ↥X = 3) (hWX : W ≤ X) : W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨n, hn⟩ := hW ⟨w, hw⟩
  have hn' : w ^ 2 ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have h1 : orderOf w ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have h2 : orderOf w ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard X (hWX hw)
    rwa [hX] at h
  have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
  have h3 : orderOf w ∣ 1 := by
    have h := Nat.dvd_gcd h1 h2
    rwa [Nat.Coprime.gcd_eq_one hcop] at h
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))

private theorem eq_of_central_displacement {G : Type*} [Group G]
    (hperf : Group.IsPerfect (G ⧸ Subgroup.center G)) (φ : G →* G)
    (hc : ∀ g : G, g⁻¹ * φ g ∈ Subgroup.center G)
    (hz : ∀ z ∈ Subgroup.center G, φ z = z) (g : G) : φ g = g := by
  haveI : IsMulCommutative (Subgroup.center G) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1)
  let D : G →* Subgroup.center G :=
    { toFun := fun g => ⟨g⁻¹ * φ g, hc g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        change (a * b)⁻¹ * φ (a * b) = (a⁻¹ * φ a) * (b⁻¹ * φ b)
        have hcommutes := (Subgroup.mem_center_iff.mp (hc a)) b⁻¹
        calc (a * b)⁻¹ * φ (a * b) = b⁻¹ * (a⁻¹ * φ a) * φ b := by rw [map_mul]; group
          _ = (a⁻¹ * φ a) * b⁻¹ * φ b := by rw [hcommutes]
          _ = (a⁻¹ * φ a) * (b⁻¹ * φ b) := mul_assoc _ _ _ }
  have hDz : ∀ z ∈ Subgroup.center G, D z = 1 := by
    intro z hzc
    apply Subtype.ext
    change z⁻¹ * φ z = 1
    rw [hz z hzc, inv_mul_cancel]
  let Dbar : G ⧸ Subgroup.center G →* Subgroup.center G :=
    QuotientGroup.lift (Subgroup.center G) D (fun z hzc => MonoidHom.mem_ker.mpr (hDz z hzc))
  have hDbar : Dbar = 1 :=
    PerfectAutomorphisms.hom_eq_one_of_commutative Dbar
  have h2 : Dbar (QuotientGroup.mk g) = 1 := by
    rw [hDbar]
    rfl
  have h3 : D g = 1 := h2
  have h4 : g⁻¹ * φ g = 1 := congrArg Subtype.val h3
  exact (inv_mul_eq_one.mp h4).symm

theorem centralizer_eq_of_isCentralProduct {Q : Type*} [Group Q] [Finite Q] {U V : Subgroup Q}
    [U.Normal] [V.Normal] (hUV : U ⊔ V = ⊤) (hc : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6))) :
    Subgroup.centralizer (U : Set Q) = V := by
  apply le_antisymm
  · intro q hq
    rw [Subgroup.mem_centralizer_iff] at hq
    obtain ⟨y, hy, v, hv, rfl⟩ := Sec14.Item148PtRes.exists_mul_eq hUV q
    have hyZ : y ∈ Sec14.Item148PtRes.centerIn U := by
      rw [Sec14.Item148PtRes.mem_centerIn_iff]
      refine ⟨hy, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_⟩
      have hgv : (g : Q) * v = v * g := Sec14.Item148PtRes.commute_of_commutator_eq_bot hc g.2 hv
      have h1 : (g : Q) * y * v = y * g * v := by
        calc (g : Q) * y * v = g * (y * v) := mul_assoc _ _ _
          _ = (y * v) * g := hq (g : Q) g.2
          _ = y * (v * g) := mul_assoc _ _ _
          _ = y * (g * v) := by rw [hgv]
          _ = y * g * v := (mul_assoc _ _ _).symm
      show (g : Q) * y = y * g
      exact mul_right_cancel h1
    have hUZ := Sec14.Item148PtRes.inf_eq_centerIn_left hc h3 hU.1
    have hyUV : y ∈ U ⊓ V := by
      rw [hUZ]
      exact hyZ
    exact V.mul_mem hyUV.2 hv
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Sec14.Item148PtRes.commute_of_commutator_eq_bot hc hu hv

theorem eq_or_eq_of_centralizer {Q : Type*} [Group Q] [Finite Q] {U V : Subgroup Q}
    [U.Normal] [V.Normal] (hUV : U ⊔ V = ⊤) (hc : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6))) {K W : Subgroup Q}
    (hKq : CFSG.IsQuasisimple ↥K) (hK : Nat.card K = 1080)
    (hZK : Nat.card (Subgroup.center ↥K) = 3) (hW : IsPGroup 2 W) (hW1 : W ≠ ⊥)
    (hWK : W ≤ Subgroup.centralizer (K : Set Q)) :
    K = U ∨ K = V := by
  have hP : Sec14.Res9Pair.IsPair U V :=
    ⟨inferInstance, inferInstance, hUV, hc, h3, hU, hV⟩
  obtain ⟨πV, hπV⟩ := exists_hom_ker_eq_right hP
  obtain ⟨πU, hπU⟩ := exists_hom_ker_eq_right hP.symm
  have hcU : Nat.card ↥U = 1080 := Sec14.Item148PtRes.card_eq_of_isTripleCover hU
  have hcV : Nat.card ↥V = 1080 := Sec14.Item148PtRes.card_eq_of_isTripleCover hV
  by_cases hKV : K ≤ V
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hKV (hcV.trans hK.symm).le)
  by_cases hKU : K ≤ U
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hKU (hcU.trans hK.symm).le)
  exfalso
  have hNV : Nat.card ↥(V.subgroupOf K) ≤ 3 := by
    rcases normal_le_center_or_eq_top_of_quasisimple (N := V.subgroupOf K) hKq with h | h
    · have hd := Subgroup.card_dvd_of_le h
      rw [hZK] at hd
      exact Nat.le_of_dvd (by norm_num) hd
    · exfalso
      apply hKV
      intro x hx
      have hm : (⟨x, hx⟩ : ↥K) ∈ V.subgroupOf K := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hm
  have hNU : Nat.card ↥(U.subgroupOf K) ≤ 3 := by
    rcases normal_le_center_or_eq_top_of_quasisimple (N := U.subgroupOf K) hKq with h | h
    · have hd := Subgroup.card_dvd_of_le h
      rw [hZK] at hd
      exact Nat.le_of_dvd (by norm_num) hd
    · exfalso
      apply hKU
      intro x hx
      have hm : (⟨x, hx⟩ : ↥K) ∈ U.subgroupOf K := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hm
  have hWV : W ≤ V := by
    intro w hw
    have hcent : ∀ k ∈ K, k * w = w * k := fun k hk =>
      Subgroup.mem_centralizer_iff.mp (hWK hw) k hk
    have hN' : Nat.card ↥(πV.ker.subgroupOf K) ≤ 3 := by
      rw [hπV]
      exact hNV
    have hw' := mem_ker_of_centralizes πV (forall_exists_mem_eq_of_card hK πV hN') hcent
    rw [hπV] at hw'
    exact hw'
  have hWU : W ≤ U := by
    intro w hw
    have hcent : ∀ k ∈ K, k * w = w * k := fun k hk =>
      Subgroup.mem_centralizer_iff.mp (hWK hw) k hk
    have hN' : Nat.card ↥(πU.ker.subgroupOf K) ≤ 3 := by
      rw [hπU]
      exact hNU
    have hw' := mem_ker_of_centralizes πU (forall_exists_mem_eq_of_card hK πU hN') hcent
    rw [hπU] at hw'
    exact hw'
  exact hW1 (eq_bot_of_isPGroup_le_of_card_eq_three hW h3 (le_inf hWU hWV))

theorem exists_mem_eq_conj {Q : Type*} [Group Q] [Finite Q] {U V : Subgroup Q}
    [U.Normal] [V.Normal] (hUV : U ⊔ V = ⊤) (hc : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6)))
    (σ : MulAut Q) (hσ3 : σ ^ 3 = 1) (hσU : ∀ u ∈ U, σ u = u) :
    ∃ v ∈ V, ∀ q : Q, σ q = v * q * v⁻¹ := by
  have hCV : Subgroup.centralizer (U : Set Q) = V :=
    centralizer_eq_of_isCentralProduct hUV hc h3 hU hV
  have hσVle : V.map σ.toMonoidHom ≤ V := by
    rintro _ ⟨x, hx, rfl⟩
    have hxC : x ∈ Subgroup.centralizer (U : Set Q) := by
      rw [hCV]
      exact hx
    show σ x ∈ V
    rw [← hCV, Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := congrArg σ (Subgroup.mem_centralizer_iff.mp hxC u hu)
    rw [map_mul, map_mul, hσU u hu] at h1
    exact h1
  have hcard : ∀ W : Subgroup Q, Nat.card (W.map σ.toMonoidHom) = Nat.card W :=
    fun W => Subgroup.card_map_of_injective σ.injective
  have hσVeq : V.map σ.toMonoidHom = V :=
    Subgroup.eq_of_le_of_card_ge hσVle (hcard V).symm.le
  set σV : MulAut ↥V := (σ.subgroupMap V).trans (MulEquiv.subgroupCongr hσVeq)
  have hσVapp : ∀ x : ↥V, (σV x : Q) = σ x := fun x => rfl
  have hσV3 : σV ^ 3 = 1 := by
    ext x
    have h1 : ((σV ^ 3) x : Q) = (σ ^ 3) (x : Q) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
      rfl
    rw [h1, hσ3]
    rfl
  set σbar : MulAut (↥V ⧸ Subgroup.center ↥V) :=
    PerfectAutomorphisms.centerQuotientHom ↥V σV with hσbardef
  have hσbar3 : σbar ^ 3 = 1 := by
    rw [hσbardef, ← map_pow, hσV3, map_one]
  obtain ⟨hZV, ⟨eV⟩⟩ := hV
  set τ : MulAut (alternatingGroup (Fin 6)) := MulAut.congr eV σbar with hτdef
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef, ← map_pow, hσbar3, map_one]
  obtain ⟨h, hh⟩ := Sec14.Item148PtRes.mem_inner_of_pow_three hτ3
  obtain ⟨vV, hvV⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥V) (eV.symm h)
  have hvh : eV (QuotientGroup.mk' (Subgroup.center ↥V) vV) = h := by
    rw [hvV, MulEquiv.apply_symm_apply]
  have hτapp : ∀ y : ↥V, τ (eV (QuotientGroup.mk' (Subgroup.center ↥V) y)) =
      eV (QuotientGroup.mk' (Subgroup.center ↥V) (σV y)) := by
    intro y
    have h1 : τ (eV (QuotientGroup.mk' (Subgroup.center ↥V) y)) =
        eV (σbar (QuotientGroup.mk' (Subgroup.center ↥V) y)) := by
      rw [hτdef]
      change eV (σbar (eV.symm (eV (QuotientGroup.mk' (Subgroup.center ↥V) y)))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h1]
    exact congrArg eV (PerfectAutomorphisms.onCenterQuotient_apply_mk σV y)
  have hkey : ∀ y : ↥V, eV (QuotientGroup.mk' (Subgroup.center ↥V) (σV y)) =
      eV (QuotientGroup.mk' (Subgroup.center ↥V) (vV * y * vV⁻¹)) := by
    intro y
    rw [← hτapp y, ← hh, MulAut.conj_apply, ← hvh]
    simp only [map_mul, map_inv]
  have hkey' : ∀ y : ↥V, (σV y)⁻¹ * (vV * y * vV⁻¹) ∈ Subgroup.center ↥V := by
    intro y
    have h2 := eV.injective (hkey y)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    exact h2
  set δV : MulAut ↥V := (MulAut.conj vV)⁻¹ * σV with hδdef
  have hδ : ∀ y : ↥V, δV y = vV⁻¹ * σV y * vV := by
    intro y
    rw [hδdef, MulAut.mul_apply, MulAut.conj_inv_apply]
  have hdisp : ∀ y : ↥V, y⁻¹ * δV y ∈ Subgroup.center ↥V := by
    intro y
    have hcZ := hkey' y
    set c := (σV y)⁻¹ * (vV * y * vV⁻¹) with hcdef
    have hcomm : vV * c⁻¹ = c⁻¹ * vV := Subgroup.mem_center_iff.mp (inv_mem hcZ) vV
    have hσy : σV y = vV * y * vV⁻¹ * c⁻¹ := by
      rw [hcdef]
      group
    have hval : y⁻¹ * δV y = c⁻¹ := by
      rw [hδ, hσy]
      calc y⁻¹ * (vV⁻¹ * (vV * y * vV⁻¹ * c⁻¹) * vV) = vV⁻¹ * c⁻¹ * vV := by group
        _ = c⁻¹ := by rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    rw [hval]
    exact inv_mem hcZ
  have hz : ∀ z ∈ Subgroup.center ↥V, δV z = z := by
    intro z hzc
    have hzU : (z : Q) ∈ U := by
      have h1 : (z : Q) ∈ U ⊓ V := by
        rw [Sec14.Item148PtRes.inf_eq_centerIn_right hc h3 hZV]
        exact Subgroup.mem_map_of_mem _ hzc
      exact h1.1
    apply Subtype.ext
    have h2 : ((δV z : ↥V) : Q) = (vV : Q)⁻¹ * σ (z : Q) * (vV : Q) := by
      rw [hδ]
      rfl
    rw [h2, hσU _ hzU]
    have hcomm : (z : Q) * vV = vV * z :=
      Sec14.Item148PtRes.commute_of_commutator_eq_bot hc hzU vV.2
    calc (vV : Q)⁻¹ * (z : Q) * (vV : Q) = (vV : Q)⁻¹ * ((z : Q) * vV) := by group
      _ = (vV : Q)⁻¹ * (vV * z) := by rw [hcomm]
      _ = z := inv_mul_cancel_left _ _
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  have hperf : Group.IsPerfect (↥V ⧸ Subgroup.center ↥V) :=
    Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
  have hid : ∀ y : ↥V, δV y = y :=
    fun y => eq_of_central_displacement hperf δV.toMonoidHom hdisp hz y
  refine ⟨(vV : Q), vV.2, fun q => ?_⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := Sec14.Item148PtRes.exists_mul_eq hUV q
  have hσw : σ w = (vV : Q) * w * (vV : Q)⁻¹ := by
    have h1 : (vV : Q)⁻¹ * σ w * (vV : Q) = w := by
      have h2 : vV⁻¹ * σV (⟨w, hw⟩ : ↥V) * vV = (⟨w, hw⟩ : ↥V) :=
        (hδ ⟨w, hw⟩).symm.trans (hid ⟨w, hw⟩)
      exact congrArg Subtype.val h2
    calc σ w = (vV : Q) * ((vV : Q)⁻¹ * σ w * (vV : Q)) * (vV : Q)⁻¹ := by group
      _ = (vV : Q) * w * (vV : Q)⁻¹ := by rw [h1]
  have hcomm : u * (vV : Q) = (vV : Q) * u :=
    Sec14.Item148PtRes.commute_of_commutator_eq_bot hc hu vV.2
  rw [map_mul, hσU u hu, hσw]
  calc u * ((vV : Q) * w * (vV : Q)⁻¹) = (u * (vV : Q)) * w * (vV : Q)⁻¹ := by group
    _ = ((vV : Q) * u) * w * (vV : Q)⁻¹ := by rw [hcomm]
    _ = (vV : Q) * (u * w) * (vV : Q)⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
