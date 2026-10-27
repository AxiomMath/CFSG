module

public import CFSG.LocalAnalysis.WeakClosure81.W16QCoreD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace KTCfg16

variable {U V₀ V I K T Q : Subgroup G}

private lemma w16q_mem_sup_of_commute {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hAC : A ≤ centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hc a ha b hb).symm
  have hle : A ≤ normalizer (B : Set G) :=
    hAC.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hcoe : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  change x ∈ ((A ⊔ B : Subgroup G) : Set G) ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x
  rw [hcoe]
  exact Set.mem_mul

private lemma w16q_isElementaryAbelian_sup_of_commute {p : ℕ} {A B : Subgroup G}
    (hA : IsElementaryAbelian p A) (hB : IsElementaryAbelian p B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElementaryAbelian p ↥(A ⊔ B) := by
  rw [CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff] at hA hB ⊢
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a1, ha1, b1, hb1, rfl⟩ := (w16q_mem_sup_of_commute hc).1 hx
    obtain ⟨a2, ha2, b2, hb2, rfl⟩ := (w16q_mem_sup_of_commute hc).1 hy
    calc (a1 * b1) * (a2 * b2)
        = a1 * (b1 * (a2 * b2)) := by group
      _ = a1 * ((b1 * a2) * b2) := by group
      _ = a1 * ((a2 * b1) * b2) := by rw [← hc a2 ha2 b1 hb1]
      _ = a1 * (a2 * (b1 * b2)) := by group
      _ = (a1 * a2) * (b1 * b2) := by group
      _ = (a2 * a1) * (b2 * b1) := by rw [hA.1 a1 ha1 a2 ha2, hB.1 b1 hb1 b2 hb2]
      _ = ((a2 * a1) * b2) * b1 := by group
      _ = (a2 * (a1 * b2)) * b1 := by group
      _ = (a2 * (b2 * a1)) * b1 := by rw [hc a1 ha1 b2 hb2]
      _ = (a2 * b2) * (a1 * b1) := by group
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (w16q_mem_sup_of_commute hc).1 hx
    rw [(show Commute a b from hc a ha b hb).mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

private lemma w16q_conj_mem_sup (h : KTCfg16 U V₀ V I K T Q) {τ z : G}
    (hτ : ∀ v ∈ V, τ * v * τ⁻¹ * v⁻¹ ∈ V₀) (hz : z ∈ U ⊔ V₀) :
    τ * z * τ⁻¹ ∈ U ⊔ V₀ := by
  have h1 : τ * z * τ⁻¹ * z⁻¹ ∈ V₀ := hτ z (h.le_V hz)
  have h2 : (τ * z * τ⁻¹ * z⁻¹) * z ∈ U ⊔ V₀ :=
    mul_mem (Subgroup.mem_sup_right h1) hz
  rwa [show (τ * z * τ⁻¹ * z⁻¹) * z = τ * z * τ⁻¹ by group] at h2

private lemma w16q_commute_conj {c x b v : G} (hxb : c * x * c⁻¹ = b)
    (hbv : b * v = v * b) : x * (c⁻¹ * v * c) = (c⁻¹ * v * c) * x := by
  have h := congrArg (fun z => c⁻¹ * z * c) hbv
  rw [← hxb] at h
  rw [show c⁻¹ * ((c * x * c⁻¹) * v) * c = x * (c⁻¹ * v * c) by group] at h
  rw [show c⁻¹ * (v * (c * x * c⁻¹)) * c = (c⁻¹ * v * c) * x by group] at h
  exact h

private lemma w16q_mem_centralizer_conj {B : Subgroup G} {c x : G}
    (hc : c ∈ normalizer (B : Set G)) (hx : x ∈ centralizer (B : Set G)) :
    c * x * c⁻¹ ∈ centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro w hw
  have hw' : c⁻¹ * w * c ∈ B := by
    simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hc) w).1 hw
  have h := hx (c⁻¹ * w * c) hw'
  have h2 := congrArg (fun z => c * z * c⁻¹) h
  rw [show c * ((c⁻¹ * w * c) * x) * c⁻¹ = w * (c * x * c⁻¹) by group] at h2
  rw [show c * (x * (c⁻¹ * w * c)) * c⁻¹ = (c * x * c⁻¹) * w by group] at h2
  exact h2

private lemma w16q_mem_of_conj_mem {A : Subgroup G} {c x : G}
    (hc : c ∈ normalizer (A : Set G)) (hx : c * x * c⁻¹ ∈ A) : x ∈ A :=
  (Subgroup.mem_normalizer_iff.1 hc x).2 hx

private lemma w16q_mem_normalizer_centralizer {B : Subgroup G} {g : G}
    (h : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer (centralizer (B : Set G) : Set G) := by
  have hz : Subgroup.zpowers g ≤ normalizer (centralizer (B : Set G) : Set G) :=
    le_normalizer_centralizer_of_le_normalizer (A := Subgroup.zpowers g) (B := B) (by
      rw [Subgroup.zpowers_le]
      exact h)
  exact hz (Subgroup.mem_zpowers g)

private lemma w16q_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun hx => ⟨(hA x).1 hx.1, (hB x).1 hx.2⟩,
         fun hx => ⟨(hA x).2 hx.1, (hB x).2 hx.2⟩⟩

theorem mem_inf_centralizer_of_map_conj (h : KTCfg16 U V₀ V I K T Q) {τ : G}
    (hτT : τ ∈ normalizer (T : Set G)) (hτV : τ ∈ normalizer (V : Set G))
    (hτ : ∀ v ∈ V, τ * v * τ⁻¹ * v⁻¹ ∈ V₀)
    (hQ₁ : I ⊔ (T ⊓ centralizer (K : Set G)) ∈ elemFamilyIn 2 T) {b : G}
    (hb : b ∈ (I ⊔ (T ⊓ centralizer (K : Set G))).map (MulAut.conj τ).toMonoidHom)
    (hbQ : b ∉ Q) : b ∈ T ⊓ centralizer (V : Set G) := by
  let Q₁ : Subgroup G := I ⊔ (T ⊓ centralizer (K : Set G))
  let B : Subgroup G := Q₁.map (MulAut.conj τ).toMonoidHom
  have hB : B ∈ elemFamilyIn 2 T := by
    dsimp [B, Q₁]
    exact map_conj_mem_elemFamilyIn 2 hτT hQ₁
  have hBT : B ≤ T := le_of_mem_elemFamilyIn hB
  have hBe : IsElementaryAbelian 2 B := isElementaryAbelian_of_mem_elemFamilyIn hB
  have hbT : b ∈ T := hBT hb
  obtain ⟨v, hvV, hyQ⟩ := h.exists_mul b hbT
  set y : G := v⁻¹ * b with hy
  have hyQ' : y ∈ Q := by rw [hy]; exact hyQ
  have hb_eq : v * y = b := by rw [hy]; group
  have hb2 : b * b = 1 := by
    have h2 := (CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff.mp hBe).2 b hb
    simpa [pow_two] using h2
  have hv2 : v * v = 1 := h.sq_V v hvV
  have hvZ : v ∉ U ⊔ V₀ := by
    intro hv
    apply hbQ
    have hvQ : v ∈ Q := h.I_le_Q (h.le_I hv)
    have hmem : v * y ∈ Q := Q.mul_mem hvQ hyQ'
    rwa [hb_eq] at hmem
  have hyvy : y * v * y = v := by
    have h3 : v * (y * v * y) = 1 := by
      calc v * (y * v * y) = (v * y) * (v * y) := by group
        _ = b * b := by rw [hb_eq]
        _ = 1 := hb2
    have h4 : v * (y * v * y) = v * v := by rw [h3, hv2]
    exact mul_left_cancel h4
  have hyv : y * v = v * y⁻¹ := by
    have h := congrArg (fun z => z * y⁻¹) hyvy
    simpa [mul_assoc] using h
  have hy2K : y * y ∈ Subgroup.centralizer (K : Set G) := h.mul_self_mem_centralizer hyQ'
  have hy2C : (y * y)⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.centralizer (K : Set G)).inv_mem hy2K
  have hyy1 : y * y = 1 := by
    have hy2V0 : (y * y)⁻¹ ∈ V₀ := by
      have hcomm : y * v * y⁻¹ * v⁻¹ = (y * y)⁻¹ := by
        rw [hyv]
        have hcy : v * (y⁻¹ * y⁻¹) = (y⁻¹ * y⁻¹) * v := by
          have h2 : v * (y*y) = (y*y) * v :=
            Subgroup.mem_centralizer_iff.1 hy2K v (h.V_le_K hvV)
          have h3 : v * (y*y)⁻¹ = (y*y)⁻¹ * v :=
            (show Commute v (y*y) from h2).inv_right
          simpa [mul_inv_rev] using h3
        rw [show v * y⁻¹ * y⁻¹ * v⁻¹ = (v * (y⁻¹ * y⁻¹)) * v⁻¹ by group]
        rw [hcy]
        group
      have hmem := h.comm_mem_V₀ y (h.Q_le_T hyQ') v hvV
      rwa [hcomm] at hmem
    have hmem : (y * y)⁻¹ ∈ V₀ ⊓ centralizer (K : Set G) := ⟨hy2V0, hy2C⟩
    have hbot : (y * y)⁻¹ ∈ (⊥ : Subgroup G) := by rwa [h.inf_eq_bot] at hmem
    have h1 : (y * y)⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have h2 := congrArg Inv.inv h1
    simpa using h2
  have hyv_comm : y * v = v * y := by
    rw [hyv, inv_eq_of_mul_eq_one_right hyy1]
  have hbv : b * v = v * b := by
    rw [← hb_eq]
    rw [show (v * y) * v = v * (y * v) by group, hyv_comm]
  obtain ⟨x, hxQ₁, hxb⟩ := Subgroup.mem_map.1 hb
  have hxb' : τ * x * τ⁻¹ = b := by
    simpa [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hxb
  have hxv : x * (τ⁻¹ * v * τ) = (τ⁻¹ * v * τ) * x := w16q_commute_conj hxb' hbv
  have hv₁V : τ⁻¹ * v * τ ∈ V := by
    simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hτV) v).1 hvV
  have hv₁Z : τ⁻¹ * v * τ ∉ U ⊔ V₀ := by
    intro hz
    apply hvZ
    have hz' := w16q_conj_mem_sup h hτ hz
    rwa [show τ * (τ⁻¹ * v * τ) * τ⁻¹ = v by group] at hz'
  have hIC : ∀ a ∈ I, ∀ c ∈ T ⊓ centralizer (K : Set G), a * c = c * a := by
    intro a ha c hc
    exact Subgroup.mem_centralizer_iff.1 hc.2 a (h.I_le_K ha)
  obtain ⟨i, hiI, c, hcC, hic⟩ := (w16q_mem_sup_of_commute hIC).1 hxQ₁
  have hc_v : c * (τ⁻¹ * v * τ) = (τ⁻¹ * v * τ) * c :=
    (Subgroup.mem_centralizer_iff.1 hcC.2 (τ⁻¹ * v * τ) (h.V_le_K hv₁V)).symm
  have hi_comm : i * (τ⁻¹ * v * τ) = (τ⁻¹ * v * τ) * i := by
    have hxv' : (i * c) * (τ⁻¹ * v * τ) = (τ⁻¹ * v * τ) * (i * c) := by
      rw [hic]; exact hxv
    have hc_inv : c⁻¹ * (τ⁻¹ * v * τ) = (τ⁻¹ * v * τ) * c⁻¹ :=
      (show Commute c (τ⁻¹ * v * τ) from hc_v).inv_left
    calc i * (τ⁻¹ * v * τ) = (i * c) * (c⁻¹ * (τ⁻¹ * v * τ)) := by group
      _ = (i * c) * ((τ⁻¹ * v * τ) * c⁻¹) := by rw [hc_inv]
      _ = ((i * c) * (τ⁻¹ * v * τ)) * c⁻¹ := by group
      _ = ((τ⁻¹ * v * τ) * (i * c)) * c⁻¹ := by rw [hxv']
      _ = (τ⁻¹ * v * τ) * i := by group
  have hiZ : i ∈ U ⊔ V₀ :=
    h.mem_of_comm (τ⁻¹ * v * τ) hv₁V hv₁Z i hiI hi_comm.symm
  have hiV : i ∈ V := h.le_V hiZ
  have hxcent : x ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [← hic]
    have hiw : i * w = w * i := h.comm_V i hiV w hw
    have hcw : c * w = w * c :=
      (Subgroup.mem_centralizer_iff.1 hcC.2 w (h.V_le_K hw)).symm
    calc w * (i * c) = (w * i) * c := by group
      _ = (i * w) * c := by rw [← hiw]
      _ = i * (w * c) := by group
      _ = i * (c * w) := by rw [← hcw]
      _ = (i * c) * w := by group
  have hbcent : b ∈ centralizer (V : Set G) := by
    have hbcent' := w16q_mem_centralizer_conj hτV hxcent
    rwa [hxb'] at hbcent'
  exact ⟨hbT, hbcent⟩

theorem map_conj_le_of_mem_elemFamilyIn (h : KTCfg16 U V₀ V I K T Q) {τ : G}
    (hτT : τ ∈ normalizer (T : Set G)) (hτV : τ ∈ normalizer (V : Set G))
    (hτ : ∀ v ∈ V, τ * v * τ⁻¹ * v⁻¹ ∈ V₀)
    (hQ₁ : I ⊔ (T ⊓ centralizer (K : Set G)) ∈ elemFamilyIn 2 T) :
    (I ⊔ (T ⊓ centralizer (K : Set G))).map (MulAut.conj τ).toMonoidHom ≤ Q := by
  let Q₁ : Subgroup G := I ⊔ (T ⊓ centralizer (K : Set G))
  let B : Subgroup G := Q₁.map (MulAut.conj τ).toMonoidHom
  let D : Subgroup G := T ⊓ centralizer (V : Set G)
  have hτC : τ ∈ normalizer (centralizer (V : Set G) : Set G) :=
    w16q_mem_normalizer_centralizer hτV
  have hτD : τ ∈ normalizer (D : Set G) := by
    have := w16q_mem_normalizer_inf hτT hτC
    simpa [D] using this
  by_contra hBQ
  obtain ⟨b₀, hb₀B, hb₀Q⟩ :=
    Set.not_subset.mp (show ¬ (B : Set G) ⊆ (Q : Set G) from hBQ)
  have hgen : ∀ b ∈ B, b ∈ D := by
    intro b hb
    by_cases hbQ : b ∈ Q
    · have hb1 : b * b₀ ∈ B := B.mul_mem hb hb₀B
      have hb1Q : b * b₀ ∉ Q := by
        intro hmem
        apply hb₀Q
        have : b⁻¹ * (b * b₀) ∈ Q := Q.mul_mem (Q.inv_mem hbQ) hmem
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      have hb0inv : b₀⁻¹ ∈ B := B.inv_mem hb₀B
      have hb0invQ : b₀⁻¹ ∉ Q := by
        intro hmem
        exact hb₀Q (by simpa using hmem)
      have h1 : b * b₀ ∈ D :=
        mem_inf_centralizer_of_map_conj h hτT hτV hτ hQ₁ hb1 hb1Q
      have h2 : b₀⁻¹ ∈ D :=
        mem_inf_centralizer_of_map_conj h hτT hτV hτ hQ₁ hb0inv hb0invQ
      have : (b * b₀) * b₀⁻¹ ∈ D := D.mul_mem h1 h2
      simpa [mul_assoc] using this
    · exact mem_inf_centralizer_of_map_conj h hτT hτV hτ hQ₁ hb hbQ
  have hBD : B ≤ D := hgen
  have hQ₁D : Q₁ ≤ D := by
    intro x hx
    have hxB : τ * x * τ⁻¹ ∈ B := by
      change τ * x * τ⁻¹ ∈ Q₁.map (MulAut.conj τ).toMonoidHom
      rw [Subgroup.mem_map]
      exact ⟨x, hx, by simp [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]⟩
    exact w16q_mem_of_conj_mem hτD (hBD hxB)
  have hID : I ≤ D := le_trans le_sup_left hQ₁D
  have hIcentV : I ≤ centralizer (V : Set G) := le_trans hID inf_le_right
  have hIZ : I ≤ U ⊔ V₀ := le_trans (le_inf le_rfl hIcentV) h.I_inf_centralizer_le
  have hZ0V : U ⊔ V₀ < V := lt_of_le_of_ne h.le_V (fun heq => h.not_le (by rw [← heq]))
  have hlt : Nat.card I < Nat.card I := by
    calc Nat.card I ≤ Nat.card ↥(U ⊔ V₀) := Subgroup.card_le_of_le hIZ
      _ < Nat.card V := Subgroup.card_lt_of_lt hZ0V
      _ = Nat.card I := h.card_eq.symm
  exact absurd hlt (lt_irrefl _)

theorem mem_normalizer_of_mem_elemFamilyIn (h : KTCfg16 U V₀ V I K T Q) {τ : G}
    (hτT : τ ∈ normalizer (T : Set G)) (hτV : τ ∈ normalizer (V : Set G))
    (hτ : ∀ v ∈ V, τ * v * τ⁻¹ * v⁻¹ ∈ V₀)
    (hQ₁ : I ⊔ (T ⊓ centralizer (K : Set G)) ∈ elemFamilyIn 2 T) :
    τ ∈ normalizer ((I ⊔ (T ⊓ centralizer (K : Set G)) : Subgroup G) : Set G) := by
  let Q₁ : Subgroup G := I ⊔ (T ⊓ centralizer (K : Set G))
  let B : Subgroup G := Q₁.map (MulAut.conj τ).toMonoidHom
  let D : Subgroup G := T ⊓ centralizer (V : Set G)
  let C : Subgroup G := T ⊓ centralizer (K : Set G)
  have hQ₁' : Q₁ ∈ elemFamilyIn 2 T := hQ₁
  obtain ⟨hQ₁T, hQ₁e, hQ₁card⟩ := mem_elemFamilyIn.1 hQ₁'
  have hB : B ∈ elemFamilyIn 2 T := by
    dsimp [B, Q₁]
    exact map_conj_mem_elemFamilyIn 2 hτT hQ₁
  have hBT : B ≤ T := le_of_mem_elemFamilyIn hB
  have hBe : IsElementaryAbelian 2 B := isElementaryAbelian_of_mem_elemFamilyIn hB
  have hBQ : B ≤ Q := map_conj_le_of_mem_elemFamilyIn h hτT hτV hτ hQ₁
  have hBcard : Nat.card B = Nat.card Q₁ := by
    dsimp [B]
    exact Subgroup.card_map_of_injective (MulAut.conj τ).injective
  have hIe : IsElementaryAbelian 2 I :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_of_le (show I ≤ Q₁ from le_sup_left) hQ₁e
  have hcomm_BI : ∀ a ∈ B, ∀ c ∈ I, a * c = c * a := by
    intro a ha c hc
    exact (Subgroup.mem_centralizer_iff.1 (h.Q_le (hBQ ha)) c hc).symm
  have hBIe : IsElementaryAbelian 2 ↥(B ⊔ I) :=
    w16q_isElementaryAbelian_sup_of_commute hBe hIe hcomm_BI
  have hBIt : B ⊔ I ≤ T := sup_le hBT (le_trans h.I_le_Q h.Q_le_T)
  have hcardBI : Nat.card ↥(B ⊔ I) ≤ 2 ^ pRank 2 T :=
    card_le_pow_pRank_of_le hBIt hBIe
  have hIleB : I ≤ B := by
    have hcard : Nat.card ↥(B ⊔ I) ≤ Nat.card B := by
      rw [hBcard, hQ₁card]
      exact hcardBI
    have heq : B = B ⊔ I := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    rw [heq]
    exact le_sup_right
  have hτC : τ ∈ normalizer (centralizer (V : Set G) : Set G) :=
    w16q_mem_normalizer_centralizer hτV
  have hτD : τ ∈ normalizer (D : Set G) := by
    have := w16q_mem_normalizer_inf hτT hτC
    simpa [D] using this
  have hle1 : B ⊓ D ≤ Q₁ ⊓ D := by
    refine le_inf ?_ inf_le_right
    exact le_trans (le_inf (le_trans inf_le_left hBQ) (le_trans inf_le_right inf_le_right))
      h.inf_centralizer_le
  have hDmap : D.map (MulAut.conj τ).toMonoidHom = D := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hτD
  have hcard_inf : Nat.card ↥(B ⊓ D) = Nat.card ↥(Q₁ ⊓ D) := by
    have hmap : (Q₁ ⊓ D).map (MulAut.conj τ).toMonoidHom = B ⊓ D := by
      rw [Subgroup.map_inf Q₁ D (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective,
        show Q₁.map (MulAut.conj τ).toMonoidHom = B from rfl, hDmap]
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj τ).injective]
  have hinf_eq : B ⊓ D = Q₁ ⊓ D :=
    Subgroup.eq_of_le_of_card_ge hle1 (le_of_eq hcard_inf.symm)
  have hC_le_D : C ≤ D := by
    refine le_inf inf_le_left ?_
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.1 hc.2 w (h.V_le_K hw)
  have hC_le_QD : C ≤ Q₁ ⊓ D := le_inf (show C ≤ Q₁ from le_sup_right) hC_le_D
  have hC_le_B : C ≤ B := by
    have : C ≤ B ⊓ D := by rw [hinf_eq]; exact hC_le_QD
    exact le_trans this inf_le_left
  have hQ₁_le_B : Q₁ ≤ B := sup_le hIleB hC_le_B
  have hQ₁B : Q₁ = B := Subgroup.eq_of_le_of_card_ge hQ₁_le_B (le_of_eq hBcard)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show Q₁.map (MulAut.conj τ).toMonoidHom = Q₁
  exact hQ₁B.symm

end KTCfg16

end CFSG.LocalAnalysis.WeakClosure81

end
