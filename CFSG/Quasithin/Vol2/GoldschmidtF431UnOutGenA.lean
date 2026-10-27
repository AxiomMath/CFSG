module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431

universe u v

structure UnGSetup {Mb : Type u} [Group Mb] {G : Type v} [Group G] (N N' : Subgroup Mb)
    (b : ↥N →* G) (b' : ↥N' →* G) (M M' : Subgroup G) : Prop where
  comp : F431Comp N N' b b'
  range : b.range = M
  range' : b'.range = M'
  cent : ∀ z ∈ centerOf (perfectCore M), orderOf z = 2 → Subgroup.centralizer ({z} : Set G) ≤ M
  norm : Subgroup.normalizer (centerOf (pCoreOf 2 M') : Set G) = M'

section Chain

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {N N' T : Subgroup Mb}
  {b : ↥N →* G} {b' : ↥N' →* G}

theorem isConj_of_fusion {x i : Mb}
    (h : Relation.ReflTransGen (fun a c : Mb => a ∈ T ∧ c ∈ T ∧
      ((∃ m ∈ N, m * a * m⁻¹ = c) ∨ (∃ m ∈ N', m * a * m⁻¹ = c))) x i) : IsConj x i := by
  induction h with
  | refl => exact IsConj.refl _
  | tail _ hs ih =>
    obtain ⟨-, -, ⟨m, -, hm⟩ | ⟨m, -, hm⟩⟩ := hs
    · exact ih.trans (isConj_iff.mpr ⟨m, hm⟩)
    · exact ih.trans (isConj_iff.mpr ⟨m, hm⟩)

theorem isConj_amalgam_of_fusion (C : F431Comp N N' b b') (hTN : T ≤ N) (hTN' : T ≤ N') {x i : Mb}
    (h : Relation.ReflTransGen (fun a c : Mb => a ∈ T ∧ c ∈ T ∧
      ((∃ m ∈ N, m * a * m⁻¹ = c) ∨ (∃ m ∈ N', m * a * m⁻¹ = c))) x i) :
    IsConj (amalgamMap b b' x) (amalgamMap b b' i) := by
  induction h with
  | refl => exact IsConj.refl _
  | @tail a c _ hs ih =>
    obtain ⟨haT, hcT, ⟨m, hm, hmc⟩ | ⟨m, hm, hmc⟩⟩ := hs
    · refine ih.trans (isConj_iff.mpr ⟨b ⟨m, hm⟩, ?_⟩)
      rw [amalgamMap_of_mem₁ b b' (hTN haT), amalgamMap_of_mem₁ b b' (hTN hcT)]
      have : (⟨c, hTN hcT⟩ : ↥N) = ⟨m, hm⟩ * ⟨a, hTN haT⟩ * ⟨m, hm⟩⁻¹ := Subtype.ext hmc.symm
      rw [this, map_mul, map_mul, map_inv]
    · refine ih.trans (isConj_iff.mpr ⟨b' ⟨m, hm⟩, ?_⟩)
      rw [amalgamMap_of_mem₂ b b' C.agree (hTN' haT), amalgamMap_of_mem₂ b b' C.agree (hTN' hcT)]
      have : (⟨c, hTN' hcT⟩ : ↥N') = ⟨m, hm⟩ * ⟨a, hTN' haT⟩ * ⟨m, hm⟩⁻¹ := Subtype.ext hmc.symm
      rw [this, map_mul, map_mul, map_inv]

theorem mul_comm_of_conj {a c g : Mb}
    (h : g * a * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * a * g⁻¹)) : a * c = c * a := by
  have e : g * (a * c) * g⁻¹ = g * (c * a) * g⁻¹ := by
    calc g * (a * c) * g⁻¹ = g * a * g⁻¹ * (g * c * g⁻¹) := by group
      _ = g * c * g⁻¹ * (g * a * g⁻¹) := h
      _ = g * (c * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel e)

end Chain

section Weak

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {N T V : Subgroup Mb} {b : ↥N →* G}

theorem weaklyClosed_img (hb : Function.Injective b) (hTN : T ≤ N) (hVT : V ≤ T)
    (hVab : ∀ a ∈ V, ∀ c ∈ V, a * c = c * a) (hVsq : ∀ a ∈ V, a ^ 2 = 1)
    (hVu : ∀ E : Subgroup Mb, E ≤ T → (∀ a ∈ E, ∀ c ∈ E, a * c = c * a) →
      (∀ a ∈ E, a ^ 2 = 1) → Nat.card E = Nat.card V → E = V) :
    IsWeaklyClosedIn (subImg b V) (subImg b T) := by
  intro g hg
  set E := conjSubgroup (subImg b V) g with hE
  have hmemE : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ subImg b V := fun x => mem_conjSubgroup_iff
  have hcardE : Nat.card E = Nat.card (subImg b V) := by
    rw [hE, conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  obtain ⟨E', hE'T, hE'E⟩ := exists_preimage hb hg
  have hE'N : E' ≤ N := hE'T.trans hTN
  have hVN : V ≤ N := hVT.trans hTN
  have hmem : ∀ x (hx : x ∈ E'), ∃ v ∈ V, ∃ hvN : v ∈ N,
      g * b ⟨x, hE'N hx⟩ * g⁻¹ = b ⟨v, hvN⟩ := by
    intro x hx
    have h1 : b ⟨x, hE'N hx⟩ ∈ E := hE'E ▸ mem_subImg_of_mem b (hE'N hx) hx
    obtain ⟨v, hvN, hvV, hv⟩ := mem_subImg.mp ((hmemE _).mp h1)
    exact ⟨v, hvV, hvN, hv.symm⟩
  have hE'V : E' = V := by
    refine hVu E' hE'T ?_ ?_ ?_
    · intro x hx y hy
      obtain ⟨v, hv, hvN, hxv⟩ := hmem x hx
      obtain ⟨w, hw, hwN, hyw⟩ := hmem y hy
      have h2 : b ⟨x, hE'N hx⟩ * b ⟨y, hE'N hy⟩ = b ⟨y, hE'N hy⟩ * b ⟨x, hE'N hx⟩ := by
        refine mul_comm_of_conj (g := g) ?_
        rw [hxv, hyw]
        exact (commute_iff_of_injective hb hwN hvN).mpr (hVab v hv w hw)
      exact (commute_iff_of_injective hb (hE'N hy) (hE'N hx)).mp h2
    · intro x hx
      obtain ⟨v, hv, hvN, hxv⟩ := hmem x hx
      refine (sq_eq_one_iff_of_injective hb (hE'N hx)).mp ?_
      have h2 : (g * b ⟨x, hE'N hx⟩ * g⁻¹) ^ 2 = 1 := by
        rw [hxv]
        exact (sq_eq_one_iff_of_injective hb hvN).mpr (hVsq v hv)
      have h3 : g * b ⟨x, hE'N hx⟩ ^ 2 * g⁻¹ = 1 := by
        rw [← h2, sq, sq]
        group
      simpa using h3
    · rw [← card_subImg hb hE'N, hE'E, hcardE, card_subImg hb hVN]
  rw [← hE'E, hE'V]

end Weak

section Main

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] [Finite G]
  {N N' : Subgroup Mb} {b : ↥N →* G} {b' : ↥N' →* G} {M M' : Subgroup G}

theorem UnGSetup.isConj_of_isConj_V (S : UnGSetup N N' b b' M M') {T V : Subgroup Mb}
    (hSyl : IsSylowTwoOf (subImg b T) ⊤) (hTN : T ≤ N) (hTN' : T ≤ N') (hVT : V ≤ T)
    (hVab : ∀ a ∈ V, ∀ c ∈ V, a * c = c * a) (hVsq : ∀ a ∈ V, a ^ 2 = 1)
    (hVeq : V = centerOf (pCoreOf 2 N'))
    (hVu : ∀ E : Subgroup Mb, E ≤ T → (∀ a ∈ E, ∀ c ∈ E, a * c = c * a) →
      (∀ a ∈ E, a ^ 2 = 1) → Nat.card E = Nat.card V → E = V)
    {v w : Mb} (hv : v ∈ V) (hw : w ∈ V) (hvN : v ∈ N) (hwN : w ∈ N)
    (h : IsConj (b ⟨v, hvN⟩) (b ⟨w, hwN⟩)) : IsConj v w := by
  have hb := S.comp.inj₁
  have hb' := S.comp.inj₂
  have hVN : V ≤ N := hVT.trans hTN
  have hVN' : V ≤ N' := hVT.trans hTN'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ (subImg b T).index := by
    have e : ((subImg b T).subgroupOf ⊤).index = (subImg b T).index :=
      Subgroup.relIndex_top_right (subImg b T)
    have h := hSyl.2.2
    rwa [e] at h
  let P : Sylow 2 G := hSyl.isPGroup.toSylow hidx
  have hP : (P : Subgroup G) = subImg b T := IsPGroup.toSylow_coe hSyl.isPGroup hidx
  have hW : IsWeaklyClosedIn (subImg b V) (P : Subgroup G) := by
    rw [hP]
    exact weaklyClosed_img hb hTN hVT hVab hVsq hVu
  have hWP : subImg b V ≤ (P : Subgroup G) := hP ▸ subImg_mono b hVT
  have hcent : ∀ x ∈ V, ∀ hxN : x ∈ N,
      b ⟨x, hxN⟩ ∈ Subgroup.centralizer (subImg b V : Set G) := by
    intro x hx hxN
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y', hy'N, hy'V, rfl⟩ := mem_subImg.mp hy
    exact (commute_iff_of_injective hb hxN hy'N).mpr (hVab y' hy'V x hx)
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨n, hn, hnv⟩ := burnside_fusion_lemma_centralizer P hWP hW (hcent v hv hvN)
    (hcent w hw hwN) (g := c⁻¹) (by rw [inv_inv]; exact hc)
  have hcen : centerOf (pCoreOf 2 M') = subImg b V := by
    rw [← S.range', ← subImg_self b', subImg_pCoreOf hb' le_rfl,
      subImg_centerOf hb' (LieType.BorelTits.pCoreOf_le 2 N'), ← hVeq]
    exact subImg_eq_of_agree (fun g h1 h2 => (S.comp.agree g h2 h1).symm) hVN' hVN
  have hnM' : n ∈ b'.range := by
    have h1 := S.norm
    rw [hcen] at h1
    rw [S.range', ← h1]
    exact hn
  obtain ⟨⟨n₀, hn₀⟩, rfl⟩ := hnM'
  rw [S.comp.agree v hvN (hVN' hv), S.comp.agree w hwN (hVN' hw)] at hnv
  have e : (⟨n₀, hn₀⟩ : ↥N')⁻¹ * ⟨v, hVN' hv⟩ * ⟨n₀, hn₀⟩ = ⟨w, hVN' hw⟩ := by
    apply hb'
    rw [map_mul, map_mul, map_inv]
    exact hnv
  have e' : n₀⁻¹ * v * n₀ = w := congrArg Subtype.val e
  exact isConj_iff.mpr ⟨n₀⁻¹, by rw [inv_inv]; exact e'⟩

theorem UnGSetup.not_isConj_zt (S : UnGSetup N N' b b' M M') {T V : Subgroup Mb} {z t : Mb}
    (hzN : z ∈ N) (htN : t ∈ N) (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ N) (hTN' : T ≤ N')
    (hzT : z ∈ T) (hz2 : orderOf z = 2) (hzZ : z ∈ centerOf (perfectCore N))
    (hcT : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w)
    (hVT : V ≤ T) (hVab : ∀ a ∈ V, ∀ c ∈ V, a * c = c * a) (hVsq : ∀ a ∈ V, a ^ 2 = 1)
    (hVeq : V = centerOf (pCoreOf 2 N'))
    (hVu : ∀ E : Subgroup Mb, E ≤ T → (∀ a ∈ E, ∀ c ∈ E, a * c = c * a) →
      (∀ a ∈ E, a ^ 2 = 1) → Nat.card E = Nat.card V → E = V)
    (hzV : z ∈ V) (htV : t ∈ V) (hnc : ¬ IsConj z t) :
    ¬ IsConj (b ⟨z, hzN⟩) (b ⟨t, htN⟩) := by
  intro h
  have hbz : Subgroup.centralizer ({b ⟨z, hzN⟩} : Set G) ≤ b.range := by
    rw [S.range]
    exact S.cent _ (map_mem_centerOf_perfectCore S.comp.inj₁ S.range hzN hzZ)
      ((orderOf_img S.comp.inj₁ hzN).trans hz2)
  have hSyl : IsSylowTwoOf (subImg b T) ⊤ :=
    lemma_F433_aux b S.comp.inj₁ hT hTN hzT hz2 hcT hbz
  exact hnc (S.isConj_of_isConj_V hSyl hTN hTN' hVT hVab hVsq hVeq hVu hzV htV hzN htN h)

end Main

end CFSG.Quasithin.H13.F431.Un
