module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPropagation

public section

namespace CFSG.Quasithin.SteinbergBN

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_conjJoin_self' (S L : Subgroup G) : L ≤ conjJoin S L := by
  intro l hl
  refine Subgroup.mem_iSup_of_mem (⟨1, one_mem S⟩ : S) ⟨l, hl, ?_⟩
  simp

theorem conjJoin_le_of_conj {S L M : Subgroup G} (h : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ M) :
    conjJoin S L ≤ M := by
  refine iSup_le fun s => ?_
  rintro _ ⟨l, hl, rfl⟩
  simpa [MulAut.conj_apply] using h s s.2 l hl

theorem conjJoin_mono_left {S₁ S₂ L : Subgroup G} (h : S₁ ≤ S₂) :
    conjJoin S₁ L ≤ conjJoin S₂ L :=
  iSup_le fun s => le_iSup_of_le (⟨s, h s.2⟩ : S₂) le_rfl

theorem mem_normalizer_of_conj {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  simpa [mul_assoc] using h' _ hx

theorem le_normalizer_conjJoin' (S L : Subgroup G) : S ≤ normalizer (conjJoin S L : Set G) := by
  have key : ∀ s ∈ S, ∀ y ∈ conjJoin S L, s * y * s⁻¹ ∈ conjJoin S L := by
    intro s hs y hy
    refine Subgroup.iSup_induction (fun s' : S => L.map (MulAut.conj (s' : G)).toMonoidHom)
      (C := fun y => s * y * s⁻¹ ∈ conjJoin S L) hy ?_ ?_ ?_
    · rintro ⟨s', hs'⟩ y ⟨x, hx, rfl⟩
      refine Subgroup.mem_iSup_of_mem (⟨s * s', mul_mem hs hs'⟩ : S) ⟨x, hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · simp
    · intro a b ha hb
      have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
  intro s hs
  exact mem_normalizer_of_conj (key s hs) fun x hx => by
    simpa using key s⁻¹ (inv_mem hs) x hx

theorem mem_normalizer_commutator' {H K : Subgroup G} {t : G} (hH : t ∈ normalizer (H : Set G))
    (hK : t ∈ normalizer (K : Set G)) : t ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (H : Set G) → g ∈ normalizer (K : Set G) →
      ∀ x ∈ ⁅H, K⁆, g * x * g⁻¹ ∈ ⁅H, K⁆ := by
    intro g hgH hgK x hx
    have hle : ⁅H, K⁆ ≤ (⁅H, K⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro h hh k hk
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : g * ⁅h, k⁆ * g⁻¹ = ⁅g * h * g⁻¹, g * k * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hgH h).1 hh)
        ((Subgroup.mem_normalizer_iff.1 hgK k).1 hk)
    exact hle hx
  exact mem_normalizer_of_conj (key t hH hK) fun x hx => by
    simpa using key t⁻¹ (inv_mem hH) (inv_mem hK) x hx

theorem eq_of_le_of_card_two {W E : Subgroup G} (hWE : W ≤ E) (hE : Nat.card E = 2)
    (hW : W ≠ ⊥) : W = E := by
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : Nat.card W ∣ 2 := hE ▸ Subgroup.card_dvd_of_le hWE
  have h1 : Nat.card W ≠ 1 := fun h => hW (Subgroup.card_eq_one.1 h)
  have h2 : Nat.card W = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h h1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hWE (by omega)

theorem exists_of_card_two {E : Subgroup G} (hE : Nat.card E = 2) :
    ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ E, x = 1 ∨ x = e := by
  obtain ⟨⟨e, he⟩, hne, huniq⟩ := (Nat.card_eq_two_iff' (1 : E)).1 hE
  refine ⟨e, he, fun h => hne (Subtype.ext h), fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr (congrArg Subtype.val (huniq ⟨x, hx⟩ fun h => hx1 (congrArg Subtype.val h)))

@[expose] def fixIn (U V : Subgroup G) (hUV : U ≤ V) (S : Set (MulAut V)) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ U, ∀ r ∈ S, r ⟨g, hUV hg⟩ = ⟨g, hUV hg⟩}
  one_mem' := ⟨one_mem U, fun r _ => map_one r⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun r hr => ?_⟩
    have e : (⟨a * b, hUV (mul_mem ha hb)⟩ : V) = ⟨a, hUV ha⟩ * ⟨b, hUV hb⟩ := rfl
    rw [e, map_mul, ha' r hr, hb' r hr]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun r hr => ?_⟩
    have e : (⟨a⁻¹, hUV (inv_mem ha)⟩ : V) = (⟨a, hUV ha⟩ : V)⁻¹ := rfl
    rw [e, map_inv, ha' r hr]

theorem mem_fixIn {U V : Subgroup G} {hUV : U ≤ V} {S : Set (MulAut V)} {g : G} :
    g ∈ fixIn U V hUV S ↔ ∃ hg : g ∈ U, ∀ r ∈ S, r ⟨g, hUV hg⟩ = ⟨g, hUV hg⟩ :=
  Iff.rfl

theorem le_normalizer_fixIn {X K U V : Subgroup G} (hKX : K ≤ X) (hUV : U ≤ V)
    (hKU : K ≤ normalizer (U : Set G)) (ρ : X →* MulAut V)
    (hρ : ∀ (x : X) (v : V), ((ρ x v : V) : G) = x * v * x⁻¹) {S : Set (MulAut V)}
    (hS : ∀ r ∈ S, ∀ k (hk : k ∈ K), r * ρ ⟨k, hKX hk⟩ = ρ ⟨k, hKX hk⟩ * r) :
    K ≤ normalizer (fixIn U V hUV S : Set G) := by
  have key : ∀ k ∈ K, ∀ g ∈ fixIn U V hUV S, k * g * k⁻¹ ∈ fixIn U V hUV S := by
    rintro k hk g ⟨hgU, hgS⟩
    have hkg : k * g * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hKU hk) g).1 hgU
    refine ⟨hkg, fun r hr => ?_⟩
    have e1 : (⟨k * g * k⁻¹, hUV hkg⟩ : V) = ρ ⟨k, hKX hk⟩ ⟨g, hUV hgU⟩ :=
      Subtype.ext (hρ ⟨k, hKX hk⟩ ⟨g, hUV hgU⟩).symm
    rw [e1, ← MulAut.mul_apply, hS r hr k hk, MulAut.mul_apply, hgS r hr]
  exact fun k hk => mem_normalizer_of_conj (key k hk) fun g hg => by
    simpa using key k⁻¹ (inv_mem hk) g hg

theorem eq_of_mem_zpowers_of_orderOf_eq_three {b c : G} (hb : orderOf b = 3)
    (hc : c ∈ Subgroup.zpowers b) : c = 1 ∨ c = b ∨ c = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rw [← zpow_mod_orderOf, hb]
  have h3 : b ^ (3 : ℤ) = 1 := by
    have := pow_orderOf_eq_one b
    rw [hb] at this
    exact_mod_cast this
  have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero b)
  · exact Or.inr (Or.inl (zpow_one b))
  · right; right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact h3

theorem commutator_conj_eq_of_sign {B : Subgroup G} {s t : G}
    (hsN : s ∈ normalizer (B : Set G)) (htN : t ∈ normalizer (B : Set G))
    (hs : (∀ b ∈ B, s * b * s⁻¹ = b) ∨ ∀ b ∈ B, s * b * s⁻¹ = b⁻¹)
    (ht : (∀ b ∈ B, t * b * t⁻¹ = b) ∨ ∀ b ∈ B, t * b * t⁻¹ = b⁻¹) {b : G} (hb : b ∈ B) :
    ⁅s, t⁆ * b * ⁅s, t⁆⁻¹ = b := by
  have inv_case : ∀ x : G, x ∈ normalizer (B : Set G) →
      ((∀ b ∈ B, x * b * x⁻¹ = b) → ∀ b ∈ B, x⁻¹ * b * x = b) ∧
      ((∀ b ∈ B, x * b * x⁻¹ = b⁻¹) → ∀ b ∈ B, x⁻¹ * b * x = b⁻¹) := by
    intro x hx
    have hmem : ∀ b ∈ B, x⁻¹ * b * x ∈ B := fun b hb => by
      simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hx) b).1 hb
    refine ⟨fun h b hb => ?_, fun h b hb => ?_⟩
    · have := h _ (hmem b hb)
      calc x⁻¹ * b * x = x * (x⁻¹ * b * x) * x⁻¹ := by rw [this]
        _ = b := by group
    · have := h _ (hmem b hb)
      calc x⁻¹ * b * x = ((x * (x⁻¹ * b * x) * x⁻¹))⁻¹ := by rw [this, inv_inv]
        _ = b⁻¹ := by group
  have e : ⁅s, t⁆ * b * ⁅s, t⁆⁻¹ = s * (t * (s⁻¹ * (t⁻¹ * b * t) * s) * t⁻¹) * s⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have hBinv : b⁻¹ ∈ B := inv_mem hb
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · rw [(inv_case t htN).1 ht b hb, (inv_case s hsN).1 hs b hb, ht b hb, hs b hb]
  · rw [(inv_case t htN).2 ht b hb, (inv_case s hsN).1 hs _ hBinv, ht _ hBinv, inv_inv,
      hs b hb]
  · rw [(inv_case t htN).1 ht b hb, (inv_case s hsN).2 hs b hb, ht _ hBinv, hs _ hBinv,
      inv_inv]
  · rw [(inv_case t htN).2 ht b hb, (inv_case s hsN).2 hs _ hBinv, inv_inv, ht b hb,
      hs _ hBinv, inv_inv]

section Config

variable [Finite G] {X T K A Q U V E : Subgroup G}

theorem a3_config_structure (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hKX : K ≤ X)
    (hK : IsShort2 K) (hK3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3)
    (hTK : T ≤ normalizer (K : Set G)) (hQ : Q = blockQ X) (hU : U = blockQ K)
    (hV : V = conjJoin X U) (hAT : A ≤ T) (hAn : T ≤ normalizer (A : Set G)) (hAU : ⁅A, U⁆ ≠ ⊥)
    (hE : E = A ⊓ centralizer (U : Set G)) (hE2 : Nat.card E = 2) :
    (Nat.card A = 4 ∧ Nat.card U = 4) ∧ U ≤ centerTorsion 2 Q ∧ ⁅Q, K⁆ = U ∧ ⁅V, K⁆ = U ∧
      (V ≤ X ∧ X ≤ normalizer (V : Set G) ∧ CFSG.IsElementaryAbelian 2 V ∧
        V ≤ centerTorsion 2 Q) ∧
      E = ⁅A, V⁆ ∧ E ≤ U ∧ U = conjJoin K E ∧ V = conjJoin X E ∧
      (∀ W : Subgroup G, W ≤ U → K ≤ normalizer (W : Set G) → W = ⊥ ∨ W = U) ∧
      U ≤ K ∧ K ≤ normalizer (U : Set G) ∧ T ≤ normalizer (U : Set G) ∧ U ≤ V ∧ V ≤ T ∧
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ (∀ v ∈ V, ∀ q ∈ Q, v * q = q * v) ∧ U ≤ Q ∧
      T ≤ normalizer (E : Set G) := by
  classical
  have hTX : T ≤ X := hT.1
  obtain ⟨hQU, hU4, hZ, -, -⟩ := short_order_three_is_alternating_four hK hK3
  have hUb : U = blockU K := hU.trans hQU
  have hUcard : Nat.card U = 4 := hUb ▸ hU4
  have hUK : U ≤ K := hU ▸ C1.blockQ_le K
  have hKU : K ≤ normalizer (U : Set G) := hU ▸ C1.le_normalizer_blockQ K
  have hirr : ∀ W : Subgroup G, W ≤ U → K ≤ normalizer (W : Set G) → W = ⊥ ∨ W = U := by
    intro W hWU hWK
    have h := hK.2.2.2.2.2 W (by rw [hZ]; exact bot_le) (hUb ▸ hWU) hWK
    rwa [hZ, ← hUb] at h
  have hKTn : K ⊔ T ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hblock : IsBlock2 (K ⊔ T) K := by
    refine ⟨hK, le_sup_left, Subgroup.Normal.isSubnormal ?_⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact hKTn
  obtain ⟨hUW, hQK, -⟩ :=
    full_Sylow_short_core_propagation hX hT le_sup_right (sup_le hKX hTX) hblock
  have hUW' : U ≤ centerTorsion 2 Q := by rw [hUb, hQ]; exact hUW
  have hQK' : ⁅Q, K⁆ = U := by rw [hQ, hUb]; exact hQK
  have hXQ : X ≤ normalizer (Q : Set G) := hQ ▸ C1.le_normalizer_blockQ X
  have hQX : Q ≤ X := hQ ▸ C1.blockQ_le X
  have hVW : V ≤ centerTorsion 2 Q := by
    rw [hV]
    exact conjJoin_le_of_conj fun x hx u hu => conj_mem_centerTorsion (hXQ hx) (hUW' hu)
  have hVQ : V ≤ Q := hVW.trans (centerTorsion_le 2 Q)
  have hVX : V ≤ X := hVQ.trans hQX
  have hXV : X ≤ normalizer (V : Set G) := hV ▸ le_normalizer_conjJoin' X U
  have hUV : U ≤ V := hV ▸ le_conjJoin_self' X U
  have hVQc : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v := fun v hv q hq =>
    ((mem_centerTorsion_iff.1 (hVW hv)).2.1 q hq).symm
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => hVQc v hv w (hVQ hw)
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => (mem_centerTorsion_iff.1 (hVW hv)).2.2
  have hVea : CFSG.IsElementaryAbelian 2 V :=
    { is_comm := ⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hVsq g g.2) }
  have hVK : ⁅V, K⁆ = U := by
    refine le_antisymm (hQK' ▸ Subgroup.commutator_mono hVQ le_rfl) ?_
    calc U = ⁅U, K⁆ := by rw [hUb]; exact (C1.commutator_blockU hK).symm
      _ ≤ ⁅V, K⁆ := Subgroup.commutator_mono hUV le_rfl
  have hTU : T ≤ normalizer (U : Set G) := fun t ht => by
    rw [← hQK']
    exact mem_normalizer_commutator' (hXQ (hTX ht)) (hTK ht)
  have hAU' : A ≤ normalizer (U : Set G) := hAT.trans hTU
  have hQT : Q ≤ T := hQ ▸ hT.pCoreOf_le
  have hVT : V ≤ T := hVQ.trans hQT
  have hAV_E : ⁅A, V⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro a ha v hv
    rw [hE, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have h1 : v * a⁻¹ * v⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.1 (hAn (hVT hv)) a⁻¹).1 (inv_mem ha)
      have e : ⁅a, v⁆ = a * (v * a⁻¹ * v⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [e]
      exact mul_mem ha h1
    · have h2 : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXV (hTX (hAT ha))) v).1 hv
      have hmem : ⁅a, v⁆ ∈ V := by
        rw [commutatorElement_def]
        exact mul_mem h2 (inv_mem hv)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hVcomm u (hUV hu) _ hmem
  have hAUV : ⁅A, U⁆ ≤ ⁅A, V⁆ := Subgroup.commutator_mono le_rfl hUV
  have hAU_E : ⁅A, U⁆ = E := eq_of_le_of_card_two (hAUV.trans hAV_E) hE2 hAU
  have hEAV : E = ⁅A, V⁆ := le_antisymm (hAU_E ▸ hAUV) hAV_E
  have hEU : E ≤ U := by
    rw [← hAU_E, Subgroup.commutator_le]
    intro a ha u hu
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hAU' ha) u).1 hu) (inv_mem hu)
  have hEV : E ≤ V := hEU.trans hUV
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE2
    omega
  have hUKE : U = conjJoin K E := by
    have hle : conjJoin K E ≤ U := conjJoin_le_of_conj fun k hk e he =>
      (Subgroup.mem_normalizer_iff.1 (hKU hk) e).1 (hEU he)
    rcases hirr _ hle (le_normalizer_conjJoin' K E) with h | h
    · exact absurd (eq_bot_iff.2 ((le_conjJoin_self' K E).trans h.le)) hEne
    · exact h.symm
  have hVXE : V = conjJoin X E := by
    apply le_antisymm
    · rw [hV]
      refine conjJoin_le_of_conj fun x hx u hu => ?_
      have hu' : u ∈ conjJoin X E := conjJoin_mono_left hKX (hUKE ▸ hu)
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjJoin' X E hx) u).1 hu'
    · exact conjJoin_le_of_conj fun x hx e he =>
        (Subgroup.mem_normalizer_iff.1 (hXV hx) e).1 (hEV he)
  have hTE : T ≤ normalizer (E : Set G) := by
    intro t ht
    refine mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
    · rw [hE, Subgroup.mem_inf] at hx ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hAn ht) x).1 hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : t⁻¹ * u * t ∈ U := by
        simpa using (Subgroup.mem_normalizer_iff.1 (hTU (inv_mem ht)) u).1 hu
      have hc := Subgroup.mem_centralizer_iff.1 hx.2 _ hu'
      calc u * (t * x * t⁻¹) = t * ((t⁻¹ * u * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * u * t)) * t⁻¹ := by rw [hc]
        _ = t * x * t⁻¹ * u := by group
    · rw [hE, Subgroup.mem_inf] at hx ⊢
      refine ⟨by simpa using (Subgroup.mem_normalizer_iff.1 (hAn (inv_mem ht)) x).1 hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : t * u * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hTU ht) u).1 hu
      have hc := Subgroup.mem_centralizer_iff.1 hx.2 _ hu'
      calc u * (t⁻¹ * x * t) = t⁻¹ * ((t * u * t⁻¹) * x) * t := by group
        _ = t⁻¹ * (x * (t * u * t⁻¹)) * t := by rw [hc]
        _ = t⁻¹ * x * t * u := by group
  have hA4 : Nat.card A = 4 := by
    obtain ⟨e, heE, he1, hEe⟩ := exists_of_card_two hE2
    have heU : e ∈ U := hEU heE
    have he2 : e * e = 1 := by
      have := hVsq e (hEV heE)
      rwa [sq] at this
    have hAe : ∀ a ∈ A, a * e * a⁻¹ = e := by
      intro a ha
      have hc : ⁅a, e⁆ ∈ E := hAU_E ▸ Subgroup.commutator_mem_commutator ha heU
      rw [commutatorElement_def] at hc
      rcases hEe _ hc with h | h
      · exact mul_inv_eq_one.1 h
      · exfalso
        have h' : a * e * a⁻¹ = 1 := by
          calc a * e * a⁻¹ = a * e * a⁻¹ * e⁻¹ * e := by group
            _ = e * e := by rw [h]
            _ = 1 := he2
        exact he1 (conj_eq_one_iff.1 h')
    have hElt : E < U := lt_of_le_of_ne hEU fun h => by
      rw [h, hUcard] at hE2
      omega
    obtain ⟨u₀, hu₀U, hu₀E⟩ := IsConcreteLE.exists_of_lt hElt
    have hAu₀ : ∀ a ∈ A, a * u₀ * a⁻¹ = u₀ ∨ a * u₀ * a⁻¹ = e * u₀ := by
      intro a ha
      have hc : ⁅a, u₀⁆ ∈ E := hAU_E ▸ Subgroup.commutator_mem_commutator ha hu₀U
      rw [commutatorElement_def] at hc
      rcases hEe _ hc with h | h
      · exact Or.inl (mul_inv_eq_one.1 h)
      · right
        calc a * u₀ * a⁻¹ = a * u₀ * a⁻¹ * u₀⁻¹ * u₀ := by group
          _ = e * u₀ := by rw [h]
    have hfix : ∀ a ∈ A, a * u₀ * a⁻¹ = u₀ → a ∈ E := by
      intro a ha hau
      let F : Subgroup G := U ⊓ centralizer ({a} : Set G)
      have hEF : E ≤ F := fun x hx => Subgroup.mem_inf.2 ⟨hEU hx, by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        rcases hEe x hx with rfl | rfl
        · simp
        · calc a * x = a * x * a⁻¹ * a := by group
            _ = x * a := by rw [hAe a ha]⟩
      have hu₀F : u₀ ∈ F := Subgroup.mem_inf.2 ⟨hu₀U, by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        calc a * u₀ = a * u₀ * a⁻¹ * a := by group
          _ = u₀ * a := by rw [hau]⟩
      have hEltF : E < F := lt_of_le_of_ne hEF fun h => hu₀E (h ▸ hu₀F)
      have h1 : Nat.card F ∣ 4 := hUcard ▸ Subgroup.card_dvd_of_le inf_le_left
      have h2 : 2 < Nat.card F := hE2 ▸ Subgroup.card_lt_of_lt hEltF
      have h3 : Nat.card F = 4 := by
        have h4 := Nat.le_of_dvd (by norm_num) h1
        interval_cases h : Nat.card F
        · exact absurd h1 (by norm_num)
        · rfl
      have hFU : F = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      rw [hE]
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : u ∈ F := hFU ▸ hu
      exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu').2) a rfl).symm
    have hAE : ¬ A ≤ E := by
      intro h
      apply hAU
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha u hu
      have hc : a ∈ centralizer (U : Set G) := (Subgroup.mem_inf.1 (hE ▸ h ha)).2
      rw [Subgroup.mem_bot, commutatorElement_def]
      have hua := Subgroup.mem_centralizer_iff.1 hc u hu
      calc a * u * a⁻¹ * u⁻¹ = (u * a) * a⁻¹ * u⁻¹ := by rw [hua]
        _ = 1 := by group
    obtain ⟨a₁, ha₁A, ha₁E⟩ := Set.not_subset.1 hAE
    have ha₁u : a₁ * u₀ * a₁⁻¹ = e * u₀ :=
      (hAu₀ a₁ ha₁A).resolve_left fun h => ha₁E (hfix a₁ ha₁A h)
    have hEA : E ≤ A := hE ▸ inf_le_left
    have hidx : (E.subgroupOf A).index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and']
      refine ⟨⟨a₁, ha₁A⟩, by rwa [Subgroup.mem_subgroupOf], fun b => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      by_cases hb : (b : G) ∈ E
      · exact Or.inr hb
      · left
        have hbu : (b : G) * u₀ * (b : G)⁻¹ = e * u₀ :=
          (hAu₀ b b.2).resolve_left fun h => hb (hfix b b.2 h)
        refine hfix _ (mul_mem ha₁A b.2) ?_
        calc ((⟨a₁, ha₁A⟩ * b : A) : G) * u₀ * ((⟨a₁, ha₁A⟩ * b : A) : G)⁻¹ =
            a₁ * ((b : G) * u₀ * (b : G)⁻¹) * a₁⁻¹ := by
              rw [Subgroup.coe_mul]
              group
          _ = (a₁ * e * a₁⁻¹) * (a₁ * u₀ * a₁⁻¹) := by rw [hbu]; group
          _ = e * (e * u₀) := by rw [hAe a₁ ha₁A, ha₁u]
          _ = u₀ := by rw [← mul_assoc, he2, one_mul]
    have hcard := (E.subgroupOf A).card_mul_index
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hE2] at hcard
    omega
  exact ⟨⟨hA4, hUcard⟩, hUW', hQK', hVK, ⟨hVX, hXV, hVea, hVW⟩, hEAV, hEU, hUKE, hVXE, hirr,
    hUK, hKU, hTU, hUV, hVT, hVcomm, hVQc, hUV.trans hVQ, hTE⟩

theorem a3_config_action (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hKX : K ≤ X)
    (hK : IsShort2 K) (hK3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3)
    (hTK : T ≤ normalizer (K : Set G)) (hQ : Q = blockQ X) (hU : U = blockQ K)
    (hV : V = conjJoin X U) (hAT : A ≤ T) (hAn : T ≤ normalizer (A : Set G)) (hAU : ⁅A, U⁆ ≠ ⊥)
    (hE : E = A ⊓ centralizer (U : Set G)) (hE2 : Nat.card E = 2) (ρ : X →* MulAut V)
    (hρ : ∀ (x : X) (v : V), ((ρ x v : V) : G) = x * v * x⁻¹) {H Tst B : Subgroup (MulAut V)}
    (hH : H = ρ.range) (hTst : Tst = (T.subgroupOf X).map ρ) (hB : B = (K.subgroupOf X).map ρ) :
    pCoreOf 2 H = ⊥ ∧ IsSylowTwoOf Tst H ∧ Nat.card B = 3 ∧
      Tst ≤ normalizer (B : Set (MulAut V)) ∧
      (∀ a : X, (a : G) ∈ A → (ρ a = 1 ↔ (a : G) ∈ E)) ∧
      ∃ τ : MulAut V, (A.subgroupOf X).map ρ = Subgroup.zpowers τ ∧
        Nat.card ((A.subgroupOf X).map ρ) = 2 ∧
        (A.subgroupOf X).map ρ ≤ Tst ⊓ centralizer (Tst : Set (MulAut V)) ∧
        τ ≠ 1 ∧ (∃ w : V, w ≠ 1 ∧ ∀ v : V, τ v = v ∨ τ v = v * w) ∧
        (∀ b ∈ B, τ * b * τ⁻¹ = b⁻¹) ∧ τ ∉ ⁅Tst, Tst⁆ ∧
        Set.range (fun v : V => ((τ v : V) : G) * (v : G)⁻¹) = (E : Set G) := by
  classical
  obtain ⟨⟨hA4, hU4⟩, -, -, hVK, ⟨-, hXV, -, -⟩, hEAV, hEU, -, -, hirr, -, hKU, -, hUV, -,
    hVcomm, hVQc, hUQ, hTE⟩ :=
    a3_config_structure hX hT hKX hK hK3 hTK hQ hU hV hAT hAn hAU hE hE2
  have hTX : T ≤ X := hT.1
  have hAX : A ≤ X := hAT.trans hTX
  have hEV : E ≤ V := hEU.trans hUV
  have hρ1 : ∀ x : X, ρ x = 1 ↔ ∀ v ∈ V, (x : G) * v * (x : G)⁻¹ = v := by
    intro x
    constructor
    · intro h v hv
      have := hρ x ⟨v, hv⟩
      rw [h] at this
      exact this.symm
    · intro h
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [hρ]
      exact h v v.2
  obtain ⟨e, heE, he1, hEe⟩ := exists_of_card_two hE2
  have heV : e ∈ V := hEV heE
  have hTe : ∀ t ∈ T, t * e * t⁻¹ = e := by
    intro t ht
    have hmem : t * e * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hTE ht) e).1 heE
    rcases hEe _ hmem with h | h
    · exact absurd (conj_eq_one_iff.1 h) he1
    · exact h
  have hTste : ∀ s ∈ Tst, s ⟨e, heV⟩ = ⟨e, heV⟩ := by
    intro s hs
    rw [hTst] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact Subtype.ext ((hρ x _).trans (hTe x hx))
  have hkerA : ∀ a : X, (a : G) ∈ A → (ρ a = 1 ↔ (a : G) ∈ E) := by
    intro a ha
    rw [hρ1]
    constructor
    · intro h
      rw [hE]
      refine Subgroup.mem_inf.2 ⟨ha, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have := h u (hUV hu)
      calc u * a = (a * u * (a : G)⁻¹) * a := by rw [this]
        _ = a * u := by group
    · intro h v hv
      rw [hVcomm _ (hEV h) v hv, mul_inv_cancel_right]
  have hTstB : Tst ≤ normalizer (B : Set (MulAut V)) := by
    intro s hs
    rw [hTst] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    have key : ∀ y : X, (y : G) ∈ T → ∀ b ∈ B, ρ y * b * (ρ y)⁻¹ ∈ B := by
      intro y hy b hb
      rw [hB] at hb ⊢
      obtain ⟨z, hz, rfl⟩ := hb
      have hz' : (z : G) ∈ K := hz
      refine ⟨y * z * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show ((y * z * y⁻¹ : X) : G) ∈ K
      exact (Subgroup.mem_normalizer_iff.1 (hTK hy) z).1 hz'
    refine mem_normalizer_of_conj (key x hx) fun b hb => ?_
    have := key x⁻¹ (inv_mem (show (x : G) ∈ T from hx)) b hb
    rwa [map_inv, inv_inv] at this
  let ρK : K →* MulAut V := ρ.comp (Subgroup.inclusion hKX)
  have hBK : B = ρK.range := by
    rw [hB]
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKX k, k.2, rfl⟩
  have hB3 : Nat.card B = 3 := by
    have hle : U.subgroupOf K ≤ ρK.ker := by
      intro k hk
      rw [MonoidHom.mem_ker]
      refine (hρ1 _).2 fun v hv => ?_
      change (k : G) * v * (k : G)⁻¹ = v
      rw [← hVQc v hv k (hUQ hk), mul_inv_cancel_right]
    have hidx : (U.subgroupOf K).index = 3 := by
      have hUK' : U.subgroupOf K = CFSG.pCore 2 K := by
        ext k
        rw [Subgroup.mem_subgroupOf, hU, blockQ_eq_map]
        exact Subgroup.mem_map_iff_mem K.subtype_injective
      rw [hUK', Subgroup.index_eq_card, hK3]
    have hdvd : ρK.ker.index ∣ 3 := hidx ▸ Subgroup.index_dvd_of_le hle
    have hne : ρK.ker.index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      have hbot : ⁅V, K⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro v hv k hk
        have hk' : k ∈ K := hk
        have : ρK ⟨k, hk'⟩ = 1 := by
          rw [← MonoidHom.mem_ker, h1]
          trivial
        have hc := (hρ1 _).1 this v hv
        rw [Subgroup.mem_bot, commutatorElement_def]
        change k * v * k⁻¹ = v at hc
        calc v * k * v⁻¹ * k⁻¹ = v * (k * v * k⁻¹)⁻¹ := by group
          _ = 1 := by rw [hc, mul_inv_cancel]
      rw [hVK] at hbot
      rw [hbot, Subgroup.card_bot] at hU4
      omega
    have h3 : ρK.ker.index = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd h hne
      · exact h
    rw [hBK, ← Subgroup.index_ker, h3]
  have hTstH : Tst ≤ H := by
    rw [hTst, hH]
    exact Subgroup.map_le_range ρ _
  have hTst2 : IsPGroup 2 Tst := by
    rw [hTst]
    exact (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm).map ρ
  have hSyl : IsSylowTwoOf Tst H := by
    refine ⟨hTstH, hTst2, fun h2 => hT.2.2 ?_⟩
    subst hH hTst
    have hmap : (T.subgroupOf X).map ρ.rangeRestrict =
        ((T.subgroupOf X).map ρ).subgroupOf ρ.range := by
      ext ⟨h, hh⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subtype.ext_iff,
        MonoidHom.coe_rangeRestrict]
    have hdvd := Subgroup.index_map_dvd (T.subgroupOf X) ρ.rangeRestrict_surjective
    rw [hmap] at hdvd
    exact h2.trans hdvd
  have hO2 : pCoreOf 2 H = ⊥ := by
    have hRH : pCoreOf 2 H ≤ H := C1.blockQ_le H
    have hR2 : IsPGroup 2 (pCoreOf 2 H) := C1.blockQ_isPGroup H
    have hHR : H ≤ normalizer (pCoreOf 2 H : Set (MulAut V)) := C1.le_normalizer_blockQ H
    have hRTst : pCoreOf 2 H ≤ Tst := hSyl.pCoreOf_le
    have hBH : B ≤ H := by
      rw [hB, hH]
      exact Subgroup.map_le_range ρ _
    have hdisj : Disjoint (pCoreOf 2 H) B := by
      apply Subgroup.disjoint_of_coprime_natCard
      obtain ⟨n, hn⟩ := hR2.exists_card_eq
      rw [hn, hB3]
      exact Nat.Coprime.pow_left n (by norm_num)
    have hRB : ∀ r ∈ pCoreOf 2 H, ∀ b ∈ B, r * b = b * r := by
      intro r hr b hb
      have hc1 : r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 H := by
        have h1 : b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.1 (hHR (hBH hb)) r⁻¹).1 (inv_mem hr)
        have e : r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) := by group
        rw [e]
        exact mul_mem hr h1
      have hc2 : r * b * r⁻¹ * b⁻¹ ∈ B := by
        have h1 : r * b * r⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hTstB (hRTst hr)) b).1 hb
        exact mul_mem h1 (inv_mem hb)
      have h1 := Subgroup.disjoint_def.1 hdisj hc1 hc2
      calc r * b = r * b * r⁻¹ * b⁻¹ * (b * r) := by group
        _ = b * r := by rw [h1, one_mul]
    have hRK : ∀ r ∈ (pCoreOf 2 H : Set (MulAut V)), ∀ k (hk : k ∈ K),
        r * ρ ⟨k, hKX hk⟩ = ρ ⟨k, hKX hk⟩ * r := fun r hr k hk =>
      hRB r hr _ (hB ▸ ⟨⟨k, hKX hk⟩, hk, rfl⟩)
    have hF := le_normalizer_fixIn hKX hUV hKU ρ hρ hRK
    have heF : e ∈ fixIn U V hUV (pCoreOf 2 H : Set (MulAut V)) :=
      ⟨hEU heE, fun r hr => hTste r (hRTst hr)⟩
    have hFU : fixIn U V hUV (pCoreOf 2 H : Set (MulAut V)) = U := by
      rcases hirr _ (fun g hg => (mem_fixIn.1 hg).1) hF with h | h
      · exact absurd (Subgroup.mem_bot.1 (h ▸ heF)) he1
      · exact h
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    have hfixV : conjJoin X U ≤ fixIn V V le_rfl {r} := by
      refine conjJoin_le_of_conj fun x hx u hu => ?_
      have hxu : x * u * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXV hx) u).1 (hUV hu)
      refine ⟨hxu, fun r' hr' => ?_⟩
      rw [Set.mem_singleton_iff.1 hr']
      have hx' : ρ ⟨x, hx⟩ ∈ H := hH ▸ ⟨⟨x, hx⟩, rfl⟩
      have hconj : (ρ ⟨x, hx⟩)⁻¹ * r * ρ ⟨x, hx⟩ ∈ pCoreOf 2 H := by
        have := (Subgroup.mem_normalizer_iff.1 (hHR (inv_mem hx')) r).1 hr
        simpa using this
      have huF : u ∈ fixIn U V hUV (pCoreOf 2 H : Set (MulAut V)) := by
        rw [hFU]
        exact hu
      obtain ⟨hu', hfu⟩ := huF
      have h1 := hfu _ hconj
      have e1 : (⟨x * u * x⁻¹, hxu⟩ : V) = ρ ⟨x, hx⟩ ⟨u, hUV hu⟩ :=
        Subtype.ext (hρ ⟨x, hx⟩ ⟨u, hUV hu⟩).symm
      rw [e1]
      calc r (ρ ⟨x, hx⟩ ⟨u, hUV hu⟩) =
          ρ ⟨x, hx⟩ (((ρ ⟨x, hx⟩)⁻¹ * r * ρ ⟨x, hx⟩) ⟨u, hUV hu⟩) := by
            simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
        _ = ρ ⟨x, hx⟩ ⟨u, hUV hu⟩ := by rw [h1]
    refine MulEquiv.ext fun v => ?_
    have hv' : (v : G) ∈ conjJoin X U := by
      rw [← hV]
      exact v.2
    obtain ⟨hv'', hv⟩ := hfixV hv'
    exact hv r rfl
  obtain ⟨a₁, ha₁A, ha₁E⟩ : ∃ a₁ ∈ A, a₁ ∉ E := by
    by_contra hcon
    push Not at hcon
    apply hAU
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha u hu
    have hc : a ∈ centralizer (U : Set G) := (Subgroup.mem_inf.1 (hE ▸ hcon a ha)).2
    rw [Subgroup.mem_bot, commutatorElement_def]
    have hua := Subgroup.mem_centralizer_iff.1 hc u hu
    calc a * u * a⁻¹ * u⁻¹ = (u * a) * a⁻¹ * u⁻¹ := by rw [hua]
      _ = 1 := by group
  let a₁' : X := ⟨a₁, hAX ha₁A⟩
  have hτ1 : ρ a₁' ≠ 1 := fun h => ha₁E ((hkerA a₁' ha₁A).1 h)
  have hτA : ρ a₁' ∈ (A.subgroupOf X).map ρ := ⟨a₁', ha₁A, rfl⟩
  have hρA2 : Nat.card ((A.subgroupOf X).map ρ) = 2 := by
    let ρA' : A →* MulAut V := ρ.comp (Subgroup.inclusion hAX)
    have hrange : (A.subgroupOf X).map ρ = ρA'.range := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨Subgroup.inclusion hAX a, a.2, rfl⟩
    have hker : ρA'.ker = E.subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hkerA _ a.2
    have hEA : E ≤ A := hE ▸ inf_le_left
    have hcard := (E.subgroupOf A).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hE2, hA4] at hcard
    rw [hrange, ← Subgroup.index_ker, hker]
    omega
  have hρAz : (A.subgroupOf X).map ρ = Subgroup.zpowers (ρ a₁') :=
    (eq_of_le_of_card_two (Subgroup.zpowers_le.2 hτA) hρA2
      fun h => hτ1 (Subgroup.zpowers_eq_bot.1 h)).symm
  have hρATst : (A.subgroupOf X).map ρ ≤ Tst := by
    rw [hTst]
    exact Subgroup.map_mono fun x hx => hAT hx
  have hρAc : (A.subgroupOf X).map ρ ≤ centralizer (Tst : Set (MulAut V)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsg : s * g * s⁻¹ ∈ (A.subgroupOf X).map ρ := by
      rw [hTst] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      obtain ⟨a, ha, rfl⟩ := hg
      have ha' : (a : G) ∈ A := ha
      have hx' : (x : G) ∈ T := hx
      refine ⟨x * a * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show ((x * a * x⁻¹ : X) : G) ∈ A
      exact (Subgroup.mem_normalizer_iff.1 (hAn hx') a).1 ha'
    obtain ⟨τ', hτ'A, hτ'1, hρAe⟩ := exists_of_card_two hρA2
    rcases hρAe g hg with h | h
    · rw [h, mul_one, one_mul]
    · rcases hρAe _ hsg with h' | h'
      · rw [h] at h'
        exact absurd (conj_eq_one_iff.1 h') hτ'1
      · rw [h] at h' ⊢
        calc s * τ' = s * τ' * s⁻¹ * s := by group
          _ = τ' * s := by rw [h']
  have hτv : ∀ v : V, ((ρ a₁' v : V) : G) = a₁ * v * a₁⁻¹ := fun v => hρ a₁' v
  have hτcases : ∀ v : V, ρ a₁' v = v ∨ ρ a₁' v = v * ⟨e, heV⟩ := by
    intro v
    have hc : ⁅a₁, (v : G)⁆ ∈ E := hEAV ▸ Subgroup.commutator_mem_commutator ha₁A v.2
    rw [commutatorElement_def] at hc
    rcases hEe _ hc with h | h
    · left
      apply Subtype.ext
      rw [hτv]
      exact mul_inv_eq_one.1 h
    · right
      apply Subtype.ext
      rw [hτv]
      calc a₁ * v * a₁⁻¹ = a₁ * v * a₁⁻¹ * (v : G)⁻¹ * v := by group
        _ = e * v := by rw [h]
        _ = v * e := hVcomm e heV v v.2
  have hrangeE : Set.range (fun v : V => ((ρ a₁' v : V) : G) * (v : G)⁻¹) = (E : Set G) := by
    ext g
    constructor
    · rintro ⟨v, rfl⟩
      change ((ρ a₁' v : V) : G) * (v : G)⁻¹ ∈ E
      rw [hτv]
      have hc : ⁅a₁, (v : G)⁆ ∈ E := hEAV ▸ Subgroup.commutator_mem_commutator ha₁A v.2
      rwa [commutatorElement_def] at hc
    · intro hg
      rcases hEe g hg with h | h
      · rw [h]
        exact ⟨1, by simp⟩
      · rw [h]
        obtain ⟨v, hv⟩ : ∃ v : V, ρ a₁' v ≠ v := by
          by_contra hcon
          push Not at hcon
          exact hτ1 (MulEquiv.ext hcon)
        refine ⟨v, ?_⟩
        have h2 := (hτcases v).resolve_left hv
        simp only [h2]
        change (v : G) * e * (v : G)⁻¹ = e
        rw [hVcomm v v.2 e heV, mul_inv_cancel_right]
  have hBne : B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b₀, hb₀B⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  have hob : orderOf b₀ = 3 := by
    have hdvd : orderOf b₀ ∣ 3 := hB3 ▸ Subgroup.orderOf_dvd_natCard B hb₀B
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hb₀1'
    · exact h
  have hBz : B = Subgroup.zpowers b₀ :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hb₀B)
      (by rw [Nat.card_zpowers, hob, hB3])).symm
  have hsign : ∀ s ∈ Tst, (∀ b ∈ B, s * b * s⁻¹ = b) ∨ ∀ b ∈ B, s * b * s⁻¹ = b⁻¹ := by
    intro s hs
    have hc : s * b₀ * s⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hTstB hs) b₀).1 hb₀B
    rw [hBz] at hc
    rcases eq_of_mem_zpowers_of_orderOf_eq_three hob hc with h | h | h
    · exact absurd (conj_eq_one_iff.1 h) hb₀1'
    · left
      intro b hb
      rw [hBz] at hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← conj_zpow, h]
    · right
      intro b hb
      rw [hBz] at hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← conj_zpow, h, inv_zpow]
  have hτinv : ∀ b ∈ B, ρ a₁' * b * (ρ a₁')⁻¹ = b⁻¹ := by
    rcases hsign _ (hρATst hτA) with hcent | hinv
    · exfalso
      have hτK : ∀ r ∈ ({ρ a₁'} : Set (MulAut V)), ∀ k (hk : k ∈ K),
          r * ρ ⟨k, hKX hk⟩ = ρ ⟨k, hKX hk⟩ * r := by
        intro r hr k hk
        rw [Set.mem_singleton_iff.1 hr]
        have hb : ρ ⟨k, hKX hk⟩ ∈ B := hB ▸ ⟨⟨k, hKX hk⟩, hk, rfl⟩
        have h1 := hcent _ hb
        calc ρ a₁' * ρ ⟨k, hKX hk⟩ = ρ a₁' * ρ ⟨k, hKX hk⟩ * (ρ a₁')⁻¹ * ρ a₁' := by group
          _ = ρ ⟨k, hKX hk⟩ * ρ a₁' := by rw [h1]
      have hF := le_normalizer_fixIn hKX hUV hKU ρ hρ hτK
      have heF : e ∈ fixIn U V hUV {ρ a₁'} := ⟨hEU heE, fun r hr => by
        rw [Set.mem_singleton_iff.1 hr]
        exact hTste _ (hρATst hτA)⟩
      have hFU : fixIn U V hUV {ρ a₁'} = U := by
        rcases hirr _ (fun g hg => (mem_fixIn.1 hg).1) hF with h | h
        · exact absurd (Subgroup.mem_bot.1 (h ▸ heF)) he1
        · exact h
      apply ha₁E
      rw [hE]
      refine Subgroup.mem_inf.2 ⟨ha₁A, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have huF : u ∈ fixIn U V hUV {ρ a₁'} := by
        rw [hFU]
        exact hu
      obtain ⟨hu', hfu⟩ := huF
      have h1 : a₁ * u * a₁⁻¹ = u := by
        have h2 := congrArg Subtype.val (hfu (ρ a₁') rfl)
        rwa [hτv] at h2
      calc u * a₁ = (a₁ * u * a₁⁻¹) * a₁ := by rw [h1]
        _ = a₁ * u := by group
    · exact hinv
  have hτcomm : ρ a₁' ∉ ⁅Tst, Tst⁆ := by
    have hle : ⁅Tst, Tst⁆ ≤ centralizer (B : Set (MulAut V)) := by
      rw [Subgroup.commutator_le]
      intro s hs t ht
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := commutator_conj_eq_of_sign (hTstB hs) (hTstB ht) (hsign s hs) (hsign t ht) hb
      calc b * ⁅s, t⁆ = ⁅s, t⁆ * b * ⁅s, t⁆⁻¹ * ⁅s, t⁆ := by rw [h1]
        _ = ⁅s, t⁆ * b := by group
    intro hτc
    have h1 := Subgroup.mem_centralizer_iff.1 (hle hτc) b₀ hb₀B
    have h2 := hτinv b₀ hb₀B
    have h3 : b₀⁻¹ = b₀ := by rw [← h2, ← h1, mul_inv_cancel_right]
    have h4 : b₀ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h3]
      exact inv_mul_cancel b₀
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hob] at h5
    norm_num at h5
  exact ⟨hO2, hSyl, hB3, hTstB, hkerA, ρ a₁', hρAz, hρA2, le_inf hρATst hρAc, hτ1,
    ⟨⟨e, heV⟩, fun h => he1 (congrArg Subtype.val h), hτcases⟩, hτinv, hτcomm, hrangeE⟩

end Config

end CFSG.Quasithin.SteinbergBN
