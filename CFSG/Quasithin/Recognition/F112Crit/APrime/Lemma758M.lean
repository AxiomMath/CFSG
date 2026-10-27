module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L : Subgroup G}

private theorem AmalgamS3.inf_normalizer_pCoreOf_eq_inf (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (h2 : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2) :
    G₂ ⊓ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) = G₁ ⊓ G₂ := by
  have hH_le : G₁ ⊓ G₂ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) :=
    (inf_le_left : G₁ ⊓ G₂ ≤ G₁).trans (le_normalizer_pCoreOf 2 G₁)
  set N : Subgroup G := G₂ ⊓ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) with hN
  have hHN : G₁ ⊓ G₂ ≤ N := le_inf inf_le_right hH_le
  have hNG₂ : N ≤ G₂ := inf_le_left
  have hrel : (G₁ ⊓ G₂).relIndex N * N.relIndex G₂ = (G₁ ⊓ G₂).relIndex G₂ :=
    Subgroup.relIndex_mul_relIndex (G₁ ⊓ G₂) N G₂ hHN hNG₂
  rw [hA.relIndex_inf_G₂] at hrel
  refine le_antisymm ?_ hHN
  have hi : (G₁ ⊓ G₂).relIndex N ∣ 3 := ⟨N.relIndex G₂, hrel.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hi with hi1 | hi3
  · exact Subgroup.relIndex_eq_one.mp hi1
  · exfalso
    have hj1 : N.relIndex G₂ = 1 := by
      rw [hi3] at hrel
      omega
    have hG₂N : G₂ ≤ N := Subgroup.relIndex_eq_one.mp hj1
    have hG₂norm : G₂ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) := hG₂N.trans inf_le_right
    have hQ₁G₀ : pCoreOf 2 G₁ ≤ G₀ := (pCoreOf_le 2 G₁).trans hA.hyp.le₁
    have hG₀norm : G₀ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) := by
      rw [hA.hyp.gen]
      exact sup_le (le_normalizer_pCoreOf 2 G₁) hG₂norm
    have hQ₁p : pCoreOf 2 G₁ ≤ pCoreOf 2 G₀ :=
      le_pCoreOf_of_le_normalizer 2 hQ₁G₀ hG₀norm (pCoreOf_isPGroup 2 G₁)
    have hQ₁bot : pCoreOf 2 G₁ = ⊥ := le_bot_iff.mp (hA.hyp.o2_trivial ▸ hQ₁p)
    have hDbot : pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ = ⊥ := by rw [hQ₁bot]; simp
    have hrel1 : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 1 := by
      rw [hDbot, hQ₁bot, Subgroup.relIndex_self]
    omega

private theorem AmalgamS3.conjSub_mem_not_mem_G₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) {k t : G}
    (hk : k ∈ G₂) (hkG₁ : k ∉ G₁) (htQ₁ : t ∈ pCoreOf 2 G₁)
    (htQ₂ : t ∉ pCoreOf 2 G₂) : k * t * k⁻¹ ∉ G₁ := by
  intro hxG₁
  have hQ₁T : pCoreOf 2 G₁ ≤ T := F7.isSylowTwoOf_pCoreOf_le hA.hyp.sylow₁
  have htT : t ∈ T := hQ₁T htQ₁
  have htG₂ : t ∈ G₂ := hA.hyp.sylow₂.1 htT
  set x : G := k * t * k⁻¹ with hxdef
  have hxG₂ : x ∈ G₂ := G₂.mul_mem (G₂.mul_mem hk htG₂) (G₂.inv_mem hk)
  have hxH : x ∈ G₁ ⊓ G₂ := ⟨by simpa [hxdef] using hxG₁, hxG₂⟩
  have hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hA.hyp.sylow₂.2.1 ⟨t, htT⟩
    have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨n, by rw [hxdef, conj_pow, htn, mul_one, mul_inv_cancel]⟩
  have hxT : x ∈ T := by
    have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
      obtain ⟨n, hn⟩ := hx2
      have hd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      refine IsPGroup.of_card (n := m) ?_
      rw [Nat.card_zpowers, hm]
    obtain ⟨g, hgH, hle⟩ := F7.isSylowTwoOf_exists_conj_le hA.hyp.sylow_inf
      (Subgroup.zpowers_le.mpr hxH) hxp
    have hgN : g ∈ Subgroup.normalizer (T : Set G) := hA.inf_le_normalizer_T hgH
    have hconj : conjSub g T = T := F7.conjSub_eq_of_mem_normalizer hgN
    have hmem : x ∈ conjSub g T := hle (Subgroup.mem_zpowers x)
    rwa [hconj] at hmem
  have hxconj : x ∈ conjSub k T := by
    rw [hxdef]
    exact mul_mem_conjSub htT
  have hne : conjSub k T ≠ T := by
    intro heq
    have hkN : k ∈ Subgroup.normalizer (T : Set G) := CosetGeom.mem_normalizer_of_conjSub_eq heq
    have hkH : k ∈ G₁ ⊓ G₂ := by
      have : k ∈ G₂ ⊓ Subgroup.normalizer (T : Set G) := ⟨hk, hkN⟩
      rwa [hA.inf_normalizer_T] at this
    exact hkG₁ hkH.1
  have hxQ₂ : x ∈ pCoreOf 2 G₂ := by
    have hinf : conjSub k T ⊓ T = pCoreOf 2 G₂ := by
      simpa [conjSub_one] using
        hA.conjSub_inf_conjSub hk (G₂.one_mem) (by simpa [conjSub_one] using hne)
    have hmem : x ∈ conjSub k T ⊓ T := ⟨hxconj, hxT⟩
    rwa [hinf] at hmem
  have hxQ₂' : t ∈ pCoreOf 2 G₂ := by
    have hDt : conjSub k⁻¹ (pCoreOf 2 G₂) = pCoreOf 2 G₂ :=
      F7.conjSub_eq_of_mem_normalizer ((le_normalizer_pCoreOf 2 G₂) (G₂.inv_mem hk))
    have hmem : k⁻¹ * x * k ∈ pCoreOf 2 G₂ := by
      have := mul_mem_conjSub (g := k⁻¹) hxQ₂
      simpa [hDt] using this
    rwa [show k⁻¹ * x * k = t by rw [hxdef]; group] at hmem
  exact htQ₂ hxQ₂'

theorem AmalgamS3.relIndex_conjClosure_pCoreOf (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (h2 : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2)
    (hD : G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) :
    (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3 := by
  set Q₁ : Subgroup G := pCoreOf 2 G₁ with hQ₁def
  set Q₂ : Subgroup G := pCoreOf 2 G₂ with hQ₂def
  set D : Subgroup G := Q₁ ⊓ Q₂ with hDdef
  set H : Subgroup G := G₁ ⊓ G₂ with hHdef
  have h2' : D.relIndex Q₁ = 2 := by
    simpa [hDdef, hQ₁def, hQ₂def] using h2
  have hD' : G₂ ≤ Subgroup.normalizer (D : Set G) := by
    simpa [hDdef, hQ₁def, hQ₂def] using hD
  have hQ₁T : Q₁ ≤ T := by
    simpa [hQ₁def] using F7.isSylowTwoOf_pCoreOf_le hA.hyp.sylow₁
  have hQ₁G₁ : Q₁ ≤ G₁ := by simpa [hQ₁def] using pCoreOf_le 2 G₁
  have hQ₁H : Q₁ ≤ H := hQ₁T.trans (hA.hyp.T_le)
  have hQ₁G₂ : Q₁ ≤ G₂ := hQ₁H.trans inf_le_right
  have hDQ₁ : D ≤ Q₁ := inf_le_left
  have hQ₂G₂ : Q₂ ≤ G₂ := pCoreOf_le 2 G₂
  have hDG₂ : D ≤ G₂ := (inf_le_right : D ≤ Q₂).trans hQ₂G₂
  have hNQ : G₂ ⊓ Subgroup.normalizer (Q₁ : Set G) = H := by
    rw [hHdef]
    simpa [hQ₁def, hQ₂def] using inf_normalizer_pCoreOf_eq_inf hA h2
  have hQ₁N : H ≤ Subgroup.normalizer (Q₁ : Set G) :=
    (inf_le_left : H ≤ G₁).trans (le_normalizer_pCoreOf 2 G₁)

  have hnot : ¬ G₂ ≤ H := by
    intro hle
    have hEq : H = G₂ := le_antisymm inf_le_right hle
    have h1 : H.relIndex G₂ = 1 := by rw [hEq, Subgroup.relIndex_self]
    rw [hHdef, hA.relIndex_inf_G₂] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨k, hkG₂, hkH⟩ := Set.not_subset.mp hnot
  have hkG₁ : k ∉ G₁ := fun h => hkH ⟨h, hkG₂⟩
  obtain ⟨t, htQ₁, htD, hall⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp h2'
  have htQ₂ : t ∉ Q₂ := fun h => htD ⟨htQ₁, h⟩
  have htH : t ∈ H := hQ₁H htQ₁
  have htG₂ : t ∈ G₂ := hQ₁G₂ htQ₁
  have htT : t ∈ T := hQ₁T htQ₁

  set t' : G := k * t * k⁻¹ with ht'def
  set s : G := t * t' with hsdef
  have ht'G₂ : t' ∈ G₂ := by
    rw [ht'def]
    exact G₂.mul_mem (G₂.mul_mem hkG₂ htG₂) (G₂.inv_mem hkG₂)
  have ht'G₁ : t' ∉ G₁ := by
    have := conjSub_mem_not_mem_G₁ hA hkG₂ hkG₁ htQ₁ (by simpa [hQ₂def] using htQ₂)
    simpa [ht'def] using this
  have ht'D : t' ∉ D := by
    intro h
    apply htD
    have hDk : conjSub k⁻¹ D = D :=
      F7.conjSub_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hD' hkG₂))
    have := mul_mem_conjSub (g := k⁻¹) h
    rwa [hDk, show k⁻¹ * t' * (k⁻¹)⁻¹ = t by rw [ht'def]; group] at this
  have hktkG₁ : k⁻¹ * t * k ∉ G₁ := by
    have hkinvG₁ : k⁻¹ ∉ G₁ := fun h => hkG₁ (by simpa using G₁.inv_mem h)
    have := conjSub_mem_not_mem_G₁ hA (G₂.inv_mem hkG₂) hkinvG₁ htQ₁
      (by simpa [hQ₂def] using htQ₂)
    simpa using this
  have hQ₁D : Q₁ = D ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · intro q hq
      rcases hall q hq with hqt | hqD
      · have hqeq : q = (q * t) * t⁻¹ := by group
        rw [hqeq]
        exact (D ⊔ Subgroup.zpowers t).mul_mem (Subgroup.mem_sup_left hqt)
          ((D ⊔ Subgroup.zpowers t).inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
      · exact Subgroup.mem_sup_left hqD
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr htQ₁)
  have hK_eq : conjSub k Q₁ = D ⊔ Subgroup.zpowers t' := by
    calc conjSub k Q₁ = conjSub k (D ⊔ Subgroup.zpowers t) := by rw [← hQ₁D]
      _ = conjSub k D ⊔ conjSub k (Subgroup.zpowers t) := conjSub_sup k D _
      _ = D ⊔ Subgroup.zpowers t' := by
        rw [F7.conjSub_eq_of_mem_normalizer (hD' hkG₂)]
        congr 1
        rw [conjSub, MonoidHom.map_zpowers]
        rfl
  set K : Subgroup G := conjSub k Q₁ with hKdef
  set P' : Subgroup G := conjSub (t * k) Q₁ with hP'def

  let Q := ↥G₂ ⧸ H.subgroupOf G₂
  have hQcard : Nat.card Q = 3 := by
    change Nat.card (↥G₂ ⧸ H.subgroupOf G₂) = 3
    simpa [H, Subgroup.relIndex, Subgroup.index] using hA.relIndex_inf_G₂
  let q1 : Q := QuotientGroup.mk (1 : ↥G₂)
  let qk : Q := QuotientGroup.mk ⟨k, hkG₂⟩
  have htkG₂ : t * k ∈ G₂ := G₂.mul_mem htG₂ hkG₂
  let qtk : Q := QuotientGroup.mk ⟨t * k, htkG₂⟩
  let qt' : Q := QuotientGroup.mk ⟨t', ht'G₂⟩
  have hq1_qk : q1 ≠ qk := by
    intro h
    have hmem : (⟨k, hkG₂⟩ : ↥G₂) ∈ H.subgroupOf G₂ := by
      simpa [q1, qk] using QuotientGroup.eq.mp h
    exact hkG₁ (Subgroup.mem_subgroupOf.mp hmem).1
  have hq1_qtk : q1 ≠ qtk := by
    intro h
    have hmem : (⟨t * k, htkG₂⟩ : ↥G₂) ∈ H.subgroupOf G₂ := by
      simpa [q1, qtk] using QuotientGroup.eq.mp h
    have htkH : t * k ∈ H := Subgroup.mem_subgroupOf.mp hmem
    have hkH : k ∈ H := by
      have := H.mul_mem (H.inv_mem htH) htkH
      simpa using this
    exact hkG₁ hkH.1
  have hqk_qtk : qk ≠ qtk := by
    intro h
    have hmem : (⟨k, hkG₂⟩ : ↥G₂)⁻¹ * ⟨t * k, htkG₂⟩ ∈ H.subgroupOf G₂ := by
      simpa [qk, qtk] using QuotientGroup.eq.mp h
    have hmemH : k⁻¹ * (t * k) ∈ H := Subgroup.mem_subgroupOf.mp hmem
    exact hktkG₁ (by simpa [mul_assoc] using hmemH.1)
  have hqt'_q1 : qt' ≠ q1 := by
    intro h
    have hmem : (⟨t', ht'G₂⟩ : ↥G₂)⁻¹ * 1 ∈ H.subgroupOf G₂ := by
      simpa [qt', q1] using QuotientGroup.eq.mp h
    have ht'invH : t'⁻¹ ∈ H := by simpa using Subgroup.mem_subgroupOf.mp hmem
    exact ht'G₁ (by simpa using (H.inv_mem ht'invH).1)
  have hqt'_qk : qt' ≠ qk := by
    intro h
    have hmem : (⟨t', ht'G₂⟩ : ↥G₂)⁻¹ * ⟨k, hkG₂⟩ ∈ H.subgroupOf G₂ := by
      simpa [qt', qk] using QuotientGroup.eq.mp h
    have hmemH : t'⁻¹ * k ∈ H := Subgroup.mem_subgroupOf.mp hmem
    have hkt'invH : k⁻¹ * t' ∈ H := by
      have := H.inv_mem hmemH
      simpa using this
    have htk'invH : t * k⁻¹ ∈ H := by
      simpa [ht'def, mul_assoc] using hkt'invH
    have hk'invH : k⁻¹ ∈ H := by
      have := H.mul_mem (H.inv_mem htH) htk'invH
      simpa using this
    have hkH : k ∈ H := by simpa using H.inv_mem hk'invH
    exact hkG₁ hkH.1
  have htriple : ({q1, qk, qtk} : Set Q) = Set.univ := by
    have htriple_ncard : ({q1, qk, qtk} : Set Q).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨q1, qk, qtk, hq1_qk, hq1_qtk, hqk_qtk, rfl⟩
    have hsub : ({q1, qk, qtk} : Set Q) ⊆ Set.univ := Set.subset_univ _
    have hle : (Set.univ : Set Q).ncard ≤ ({q1, qk, qtk} : Set Q).ncard := by
      rw [Set.ncard_univ, hQcard, htriple_ncard]
    exact Set.eq_of_subset_of_ncard_le hsub hle
  have hclass_case : ∀ g ∈ G₂,
      (∃ h ∈ H, g = h) ∨ (∃ h ∈ H, g = k * h) ∨ (∃ h ∈ H, g = (t * k) * h) := by
    intro g hg
    let qg : Q := QuotientGroup.mk ⟨g, hg⟩
    have hqg : qg ∈ ({q1, qk, qtk} : Set Q) := by
      rw [htriple]
      exact Set.mem_univ qg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hqg
    rcases hqg with h | h | h
    · left
      have hmem : (⟨g, hg⟩ : ↥G₂) ∈ H.subgroupOf G₂ := by
        simpa [qg, q1] using QuotientGroup.eq.mp h
      have hgH : g ∈ H := by
        have hginv : g⁻¹ ∈ H := by
          simpa using Subgroup.mem_subgroupOf.mp hmem
        simpa using H.inv_mem hginv
      exact ⟨g, hgH, rfl⟩
    · right; left
      have hmem : (⟨g, hg⟩ : ↥G₂)⁻¹ * ⟨k, hkG₂⟩ ∈ H.subgroupOf G₂ := by
        simpa [qg, qk] using QuotientGroup.eq.mp h
      have hmemH : g⁻¹ * k ∈ H := Subgroup.mem_subgroupOf.mp hmem
      refine ⟨(g⁻¹ * k)⁻¹, H.inv_mem hmemH, ?_⟩
      group
    · right; right
      have hmem : (⟨g, hg⟩ : ↥G₂)⁻¹ * ⟨t * k, htkG₂⟩ ∈ H.subgroupOf G₂ := by
        simpa [qg, qtk] using QuotientGroup.eq.mp h
      have hmemH : g⁻¹ * (t * k) ∈ H := Subgroup.mem_subgroupOf.mp hmem
      refine ⟨(g⁻¹ * (t * k))⁻¹, H.inv_mem hmemH, ?_⟩
      group
  have hconj_cases : ∀ g ∈ G₂,
      conjSub g Q₁ = Q₁ ∨ conjSub g Q₁ = K ∨ conjSub g Q₁ = P' := by
    intro g hg
    rcases hclass_case g hg with ⟨h, hhH, rfl⟩ | ⟨h, hhH, rfl⟩ | ⟨h, hhH, rfl⟩
    · left
      exact F7.conjSub_eq_of_mem_normalizer (hQ₁N hhH)
    · right; left
      rw [hKdef, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hQ₁N hhH)]
    · right; right
      rw [hP'def, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hQ₁N hhH)]

  set x : G := t * t' * t⁻¹ with hxdef
  set y : G := t' * t * t'⁻¹ with hydef
  have hxP' : x ∈ P' := by
    have hx_eq : x = (t * k) * t * (t * k)⁻¹ := by
      rw [hxdef, ht'def]
      group
    rw [hP'def, hx_eq]
    exact mul_mem_conjSub htQ₁
  have hyPy : y ∈ conjSub t' Q₁ := by
    have h := mul_mem_conjSub (g := t') (H := Q₁) htQ₁
    simpa [hydef] using h
  have hPy_ne_Q₁ : conjSub t' Q₁ ≠ Q₁ := by
    intro h
    have ht'N : t' ∈ Subgroup.normalizer (Q₁ : Set G) := CosetGeom.mem_normalizer_of_conjSub_eq h
    have ht'H : t' ∈ H := by
      have : t' ∈ G₂ ⊓ Subgroup.normalizer (Q₁ : Set G) := ⟨ht'G₂, ht'N⟩
      rwa [hNQ] at this
    exact ht'G₁ ht'H.1
  have hPy_ne_K : conjSub t' Q₁ ≠ K := by
    intro h
    have hconj : conjSub (k⁻¹ * t') Q₁ = Q₁ := by
      calc conjSub (k⁻¹ * t') Q₁ = conjSub k⁻¹ (conjSub t' Q₁) := conjSub_mul ..
        _ = conjSub k⁻¹ K := by rw [h]
        _ = conjSub (k⁻¹ * k) Q₁ := by rw [hKdef, ← conjSub_mul]
        _ = Q₁ := by rw [inv_mul_cancel, conjSub_one]
    have htk' : t * k⁻¹ ∈ Subgroup.normalizer (Q₁ : Set G) := by
      have := CosetGeom.mem_normalizer_of_conjSub_eq hconj
      simpa [ht'def, mul_assoc] using this
    have htN : t ∈ Subgroup.normalizer (Q₁ : Set G) := hQ₁N htH
    have hk'invN : k⁻¹ ∈ Subgroup.normalizer (Q₁ : Set G) := by
      have := (Subgroup.normalizer (Q₁ : Set G)).mul_mem
        ((Subgroup.normalizer (Q₁ : Set G)).inv_mem htN) htk'
      simpa using this
    have hkN : k ∈ Subgroup.normalizer (Q₁ : Set G) := by
      simpa using (Subgroup.normalizer (Q₁ : Set G)).inv_mem hk'invN
    have hkH : k ∈ H := by
      have : k ∈ G₂ ⊓ Subgroup.normalizer (Q₁ : Set G) := ⟨hkG₂, hkN⟩
      rwa [hNQ] at this
    exact hkG₁ hkH.1
  have hPy_eq : conjSub t' Q₁ = P' := by
    rcases hconj_cases t' ht'G₂ with h | h | h
    · exact absurd h hPy_ne_Q₁
    · exact absurd h hPy_ne_K
    · exact h
  have hyP' : y ∈ P' := by
    rw [← hPy_eq]
    exact hyPy
  have hDrelP' : D.relIndex P' = 2 := by
    rw [hP'def]
    have hmap := Subgroup.relIndex_map_map_of_injective
      (f := (MulAut.conj (t * k)).toMonoidHom) D Q₁
      (MulEquiv.injective (MulAut.conj (t * k)))
    have hDmap : D.map (MulAut.conj (t * k)).toMonoidHom = D := by
      simpa [conjSub] using
        F7.conjSub_eq_of_mem_normalizer (hD' (G₂.mul_mem htG₂ hkG₂))
    rw [hDmap, h2'] at hmap
    simpa [conjSub] using hmap
  have ht2D : t * t ∈ D := by
    have h2idx : (D.subgroupOf Q₁).index = 2 := h2'
    have h : (⟨t, htQ₁⟩ : ↥Q₁) ^ 2 ∈ D.subgroupOf Q₁ :=
      Subgroup.sq_mem_of_index_two (H := D.subgroupOf Q₁) h2idx ⟨t, htQ₁⟩
    simpa [Subgroup.mem_subgroupOf, pow_two] using h
  have ht'2D : t' * t' ∈ D := by
    have h : k * (t * t) * k⁻¹ ∈ D := by
      have hconj : conjSub k D = D := F7.conjSub_eq_of_mem_normalizer (hD' hkG₂)
      rw [← hconj]
      exact mul_mem_conjSub ht2D
    rwa [show k * (t * t) * k⁻¹ = t' * t' by rw [ht'def]; group] at h
  have hxG₂ : x ∈ G₂ := by
    rw [hxdef]
    exact G₂.mul_mem (G₂.mul_mem htG₂ ht'G₂) (G₂.inv_mem htG₂)
  have hyG₂ : y ∈ G₂ := by
    rw [hydef]
    exact G₂.mul_mem (G₂.mul_mem ht'G₂ htG₂) (G₂.inv_mem ht'G₂)
  have hxD : x ∉ D := by
    intro hx
    apply ht'D
    have hDt : conjSub t⁻¹ D = D :=
      F7.conjSub_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hD' htG₂))
    have := mul_mem_conjSub (g := t⁻¹) hx
    rwa [hDt, show t⁻¹ * x * (t⁻¹)⁻¹ = t' by rw [hxdef]; group] at this
  have hyD : y ∉ D := by
    intro hy
    apply htD
    have hDt : conjSub t'⁻¹ D = D :=
      F7.conjSub_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hD' ht'G₂))
    have := mul_mem_conjSub (g := t'⁻¹) hy
    rwa [hDt, show t'⁻¹ * y * (t'⁻¹)⁻¹ = t by rw [hydef]; group] at this
  have hxyinv : x * y⁻¹ ∈ D :=
    CFSG.Quasithin.F6.GoldAmL3.mul_inv_mem_of_relIndex_eq_two hDrelP' hxP' hyP' hxD hyD
  have hy2D : y * y ∈ D := by
    have h : (⟨y, hyP'⟩ : ↥P') ^ 2 ∈ D.subgroupOf P' :=
      Subgroup.sq_mem_of_index_two (H := D.subgroupOf P') (by exact hDrelP') ⟨y, hyP'⟩
    simpa [Subgroup.mem_subgroupOf, pow_two] using h
  have hxyD : x * y ∈ D := by
    have := D.mul_mem hxyinv hy2D
    rwa [show (x * y⁻¹) * (y * y) = x * y by group] at this

  have hsG₂ : s ∈ G₂ := G₂.mul_mem htG₂ ht'G₂
  haveI : (D.subgroupOf G₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDG₂).2 hD'
  let πd : ↥G₂ →* (↥G₂ ⧸ D.subgroupOf G₂) := QuotientGroup.mk' (D.subgroupOf G₂)
  let Tbar : (↥G₂ ⧸ D.subgroupOf G₂) := πd ⟨t, htG₂⟩
  let T'bar : (↥G₂ ⧸ D.subgroupOf G₂) := πd ⟨t', ht'G₂⟩
  have hTbar2 : Tbar ^ 2 = 1 := by
    have hmem : (⟨t, htG₂⟩ : ↥G₂) ^ 2 ∈ D.subgroupOf G₂ := by
      simpa [Subgroup.mem_subgroupOf, pow_two] using ht2D
    have h := (QuotientGroup.eq_one_iff (N := D.subgroupOf G₂)
      (x := (⟨t, htG₂⟩ : ↥G₂) ^ 2)).2 hmem
    simpa only [Tbar, πd, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow] using h
  have hT'bar2 : T'bar ^ 2 = 1 := by
    have hmem : (⟨t', ht'G₂⟩ : ↥G₂) ^ 2 ∈ D.subgroupOf G₂ := by
      simpa [Subgroup.mem_subgroupOf, pow_two] using ht'2D
    have h := (QuotientGroup.eq_one_iff (N := D.subgroupOf G₂)
      (x := (⟨t', ht'G₂⟩ : ↥G₂) ^ 2)).2 hmem
    simpa only [T'bar, πd, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow] using h
  have hTinv : Tbar⁻¹ = Tbar := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hTbar2)
  have hT'inv : T'bar⁻¹ = T'bar :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hT'bar2)
  have hprod : πd ⟨x, hxG₂⟩ * πd ⟨y, hyG₂⟩ = 1 := by
    rw [← map_mul]
    have hmem : (⟨x, hxG₂⟩ * ⟨y, hyG₂⟩ : ↥G₂) ∈ D.subgroupOf G₂ := by
      simpa [Subgroup.mem_subgroupOf] using hxyD
    exact (QuotientGroup.eq_one_iff (N := D.subgroupOf G₂)
      (x := (⟨x, hxG₂⟩ * ⟨y, hyG₂⟩ : ↥G₂))).2 hmem
  have hxbar : πd ⟨x, hxG₂⟩ = Tbar * T'bar * Tbar := by
    have hx_eq : (⟨x, hxG₂⟩ : ↥G₂) =
        ⟨t, htG₂⟩ * ⟨t', ht'G₂⟩ * (⟨t, htG₂⟩)⁻¹ := by
      apply Subtype.ext
      change x = t * t' * t⁻¹
      rw [hxdef]
    rw [hx_eq, map_mul, map_mul, map_inv, hTinv]
  have hybar : πd ⟨y, hyG₂⟩ = T'bar * Tbar * T'bar := by
    have hy_eq : (⟨y, hyG₂⟩ : ↥G₂) =
        ⟨t', ht'G₂⟩ * ⟨t, htG₂⟩ * (⟨t', ht'G₂⟩)⁻¹ := by
      apply Subtype.ext
      change y = t' * t * t'⁻¹
      rw [hydef]
    rw [hy_eq, map_mul, map_mul, map_inv, hT'inv]
  have hsbar : πd ⟨s, hsG₂⟩ = Tbar * T'bar := by
    have hs_eq : (⟨s, hsG₂⟩ : ↥G₂) = ⟨t, htG₂⟩ * ⟨t', ht'G₂⟩ := by
      apply Subtype.ext
      change s = t * t'
      rw [hsdef]
    rw [hs_eq, map_mul]
  have hS3 : (Tbar * T'bar) ^ 3 = 1 := by
    have hcalc : (Tbar * T'bar) ^ 3 = πd ⟨x, hxG₂⟩ * πd ⟨y, hyG₂⟩ := by
      rw [hxbar, hybar]
      rw [pow_succ, pow_succ, pow_one]
      group
    rw [hcalc]
    exact hprod
  have hs3G₂ : s ^ 3 ∈ G₂ := G₂.pow_mem hsG₂ 3
  have hs3bar : πd ⟨s ^ 3, hs3G₂⟩ = 1 := by
    have hs3_eq : (⟨s ^ 3, hs3G₂⟩ : ↥G₂) = (⟨s, hsG₂⟩ : ↥G₂) ^ 3 := Subtype.ext rfl
    rw [hs3_eq, map_pow, hsbar, hS3]
  have hs3D : s ^ 3 ∈ D := by
    have hmem : (⟨s ^ 3, hs3G₂⟩ : ↥G₂) ∈ D.subgroupOf G₂ :=
      (QuotientGroup.eq_one_iff (N := D.subgroupOf G₂)
        (x := (⟨s ^ 3, hs3G₂⟩ : ↥G₂))).1 (by
          simpa only [πd, QuotientGroup.mk'_apply] using hs3bar)
    exact Subgroup.mem_subgroupOf.mp hmem
  have hsD : s ∉ D := by
    intro hs
    have ht'Q₁ : t' ∈ Q₁ := by
      have : t' = t⁻¹ * s := by rw [hsdef]; group
      rw [this]
      exact Q₁.mul_mem (Q₁.inv_mem htQ₁) (hDQ₁ hs)
    have hKleQ₁ : conjSub k Q₁ ≤ Q₁ := by
      rw [← hKdef, hK_eq]
      exact sup_le hDQ₁ (Subgroup.zpowers_le.mpr ht'Q₁)
    have hKeq : conjSub k Q₁ = Q₁ :=
      Subgroup.eq_of_le_of_card_ge hKleQ₁ (le_of_eq (CosetGeom.card_conjSub k Q₁).symm)
    have hkN : k ∈ Subgroup.normalizer (Q₁ : Set G) := CosetGeom.mem_normalizer_of_conjSub_eq hKeq
    have hkH : k ∈ H := by
      have : k ∈ G₂ ⊓ Subgroup.normalizer (Q₁ : Set G) := ⟨hkG₂, hkN⟩
      rwa [hNQ] at this
    exact hkG₁ hkH.1

  set P : Subgroup G := D ⊔ Subgroup.zpowers s with hPdef
  have hDP : D ≤ P := by rw [hPdef]; exact le_sup_left
  have hsP : s ∈ P := by rw [hPdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hP_G₂ : P ≤ G₂ := sup_le hDG₂ (Subgroup.zpowers_le.mpr hsG₂)
  have hDnP : (D.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDP).2 (hP_G₂.trans hD')
  let sP : ↥P := ⟨s, hsP⟩
  have hzP : (Subgroup.zpowers s).subgroupOf P = Subgroup.zpowers sP := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  have hsupP : (D.subgroupOf P) ⊔ Subgroup.zpowers sP = ⊤ := by
    rw [← hzP]
    rw [← Subgroup.subgroupOf_sup hDP (Subgroup.zpowers_le.mpr hsP)]
    rw [← hPdef]
    exact Subgroup.subgroupOf_self P
  haveI : (D.subgroupOf P).Normal := hDnP
  let πP : ↥P →* (↥P ⧸ D.subgroupOf P) := QuotientGroup.mk' (D.subgroupOf P)
  let sp : (↥P ⧸ D.subgroupOf P) := πP sP
  have hsp3 : sp ^ 3 = 1 := by
    change (πP sP) ^ 3 = 1
    have hsP3 : sP ^ 3 = ⟨s ^ 3, hDP hs3D⟩ := Subtype.ext rfl
    rw [← map_pow, hsP3]
    exact (QuotientGroup.eq_one_iff (N := D.subgroupOf P)
      (x := (⟨s ^ 3, hDP hs3D⟩ : ↥P))).2 (by
        simpa [Subgroup.mem_subgroupOf] using hs3D)
  have hspne : sp ≠ 1 := by
    intro h
    have h' : πP sP = 1 := by simpa [sp] using h
    have hmem : sP ∈ D.subgroupOf P :=
      (QuotientGroup.eq_one_iff (N := D.subgroupOf P) (x := sP)).1 h'
    exact hsD (Subgroup.mem_subgroupOf.mp hmem)
  have hord : orderOf sp = 3 := orderOf_eq_prime hsp3 hspne
  have hKmap : (D.subgroupOf P).map πP = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap := congrArg (Subgroup.map πP) hsupP
  rw [Subgroup.map_sup, MonoidHom.map_zpowers,
    Subgroup.map_top_of_surjective πP (QuotientGroup.mk'_surjective _),
    hKmap, bot_sup_eq] at hmap
  have hgen : Subgroup.zpowers sp = ⊤ := by
    simpa [sp] using hmap
  have hcardQp : Nat.card (↥P ⧸ D.subgroupOf P) = 3 := by
    calc Nat.card (↥P ⧸ D.subgroupOf P) =
        Nat.card (⊤ : Subgroup (↥P ⧸ D.subgroupOf P)) := (Subgroup.card_top).symm
      _ = Nat.card (Subgroup.zpowers sp) := by rw [← hgen]
      _ = orderOf sp := Nat.card_zpowers sp
      _ = 3 := hord
  have hDrelP : D.relIndex P = 3 := hcardQp

  have htNP : t ∈ Subgroup.normalizer (P : Set G) := by
    have hts : t * s * t⁻¹ ∈ P := by
      have hd : t * t * (t' * t') ∈ D := D.mul_mem ht2D ht'2D
      have he : t * s * t⁻¹ = (t * t * (t' * t')) * s⁻¹ := by
        rw [hsdef]
        group
      rw [he]
      exact P.mul_mem (hDP hd) (P.inv_mem hsP)
    have hconjP : conjSub t P ≤ P := by
      calc conjSub t P = conjSub t D ⊔ conjSub t (Subgroup.zpowers s) := by
            rw [hPdef, conjSub_sup]
        _ = D ⊔ Subgroup.zpowers (t * s * t⁻¹) := by
            rw [F7.conjSub_eq_of_mem_normalizer (hD' htG₂)]
            congr 1
            rw [conjSub, MonoidHom.map_zpowers]
            rfl
        _ ≤ P := sup_le hDP (Subgroup.zpowers_le.mpr hts)
    have hcardP : Nat.card P ≤ Nat.card (conjSub t P) :=
      le_of_eq (CosetGeom.card_conjSub t P).symm
    have heq : conjSub t P = P := Subgroup.eq_of_le_of_card_ge hconjP hcardP
    exact CosetGeom.mem_normalizer_of_conjSub_eq heq
  have hQN : Q₁ ≤ Subgroup.normalizer (P : Set G) := by
    rw [hQ₁D]
    exact sup_le (hDP.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr htNP)
  have hQ₁_inf_P : Q₁ ⊓ P = D := by
    have hDX : D ≤ Q₁ ⊓ P := le_inf hDQ₁ hDP
    have hXQ₁ : Q₁ ⊓ P ≤ Q₁ := inf_le_left
    have hXP : Q₁ ⊓ P ≤ P := inf_le_right
    have hdvd2 : D.relIndex (Q₁ ⊓ P) ∣ 2 := by
      have h := Subgroup.relIndex_mul_relIndex D (Q₁ ⊓ P) Q₁ hDX hXQ₁
      rw [h2'] at h
      exact ⟨(Q₁ ⊓ P).relIndex Q₁, h.symm⟩
    have hdvd3 : D.relIndex (Q₁ ⊓ P) ∣ 3 := by
      have h := Subgroup.relIndex_mul_relIndex D (Q₁ ⊓ P) P hDX hXP
      rw [hDrelP] at h
      exact ⟨(Q₁ ⊓ P).relIndex P, h.symm⟩
    have hrelX : D.relIndex (Q₁ ⊓ P) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
      · exact h1
      · exfalso
        have hle : D.relIndex (Q₁ ⊓ P) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
        omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hrelX) hDX

  have ht'K : t' ∈ K := by
    rw [hKdef]
    have := mul_mem_conjSub (g := k) (H := Q₁) htQ₁
    simpa [ht'def] using this
  have hP_le_sup : P ≤ Q₁ ⊔ K := by
    rw [hPdef]
    refine sup_le (hDQ₁.trans le_sup_left) ?_
    rw [Subgroup.zpowers_le]
    exact (Q₁ ⊔ K).mul_mem (Subgroup.mem_sup_left htQ₁) (Subgroup.mem_sup_right ht'K)
  have ht'_sup : t' ∈ Q₁ ⊔ P := by
    have ht'eq : t' = t⁻¹ * s := by rw [hsdef]; group
    rw [ht'eq]
    exact (Q₁ ⊔ P).mul_mem (Subgroup.mem_sup_left (Q₁.inv_mem htQ₁))
      (Subgroup.mem_sup_right hsP)
  have hK_le_sup : K ≤ Q₁ ⊔ P := by
    rw [hK_eq]
    exact sup_le (hDQ₁.trans le_sup_left) (Subgroup.zpowers_le.mpr ht'_sup)
  have hsup_eq : Q₁ ⊔ P = Q₁ ⊔ K :=
    le_antisymm (sup_le le_sup_left hP_le_sup) (sup_le le_sup_left hK_le_sup)
  have hMain : Q₁.relIndex (Q₁ ⊔ K) = 3 := by
    rw [← hsup_eq]
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := Q₁) (K := P) hQN).1
    rw [hQ₁_inf_P, hDrelP] at h
    exact h

  have hconj_eq : conjClosure Q₁ G₂ = Q₁ ⊔ K := by
    apply le_antisymm
    · refine conjClosure_le ?_
      intro g hg z hz
      have hmem : g * z * g⁻¹ ∈ conjSub g Q₁ := mul_mem_conjSub hz
      rcases hconj_cases g hg with h | h | h
      · rw [h] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [h] at hmem
        exact Subgroup.mem_sup_right hmem
      · rw [h] at hmem
        have hsub : P' ≤ Q₁ ⊔ K := by
          rw [hP'def]
          calc conjSub (t * k) Q₁ = conjSub t (conjSub k Q₁) := conjSub_mul ..
            _ = conjSub t K := by rw [hKdef]
            _ ≤ Q₁ ⊔ K := by
                intro x hx
                rw [mem_conjSub] at hx
                have hxK : t⁻¹ * x * t ∈ K := hx
                have hxeq : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
                rw [hxeq]
                exact (Q₁ ⊔ K).mul_mem ((Q₁ ⊔ K).mul_mem
                  (Subgroup.mem_sup_left htQ₁) (Subgroup.mem_sup_right hxK))
                  ((Q₁ ⊔ K).inv_mem (Subgroup.mem_sup_left htQ₁))
        exact hsub hmem
    · refine sup_le (le_conjClosure Q₁ G₂) ?_
      intro x hx
      rw [hKdef] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact mem_conjClosure hkG₂ hz
  rw [hconj_eq]
  exact hMain

end CFSG.Quasithin.F112Crit.APrime

end
