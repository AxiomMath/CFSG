module

public import CFSG.Quasithin.Vol2.KGFactG2RuAbs

public section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q] {P T W V : Subgroup Q} {x : Q} {ns : List Q}
  {a : ℕ → Q} {G : Type} [Group G] [Finite G] {K : Subgroup G} {ψ : ↥K →* Q}
  {B : Subgroup G}

omit [Finite Q] in
theorem kgg2_of_le_zK {S W₀ : Subgroup G} (hBK : B ≤ K) (hS : IsSylowTwoOf S B)
    (hW : Nat.card W₀ = 64) (hWZ : W₀ ≤ zK K) {k : ↥K}
    (hk : (k : G) ∉ Subgroup.normalizer (B : Set G)) :
    ∃ V₃ : Subgroup G, V₃ ≤ W₀ ∧ Nat.card V₃ = 8 ∧ S ≤ Subgroup.normalizer (V₃ : Set G) ∧
      ¬ K ⊓ Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V', hV'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥W₀) 2 (n := 3)
    (by rw [hW]; norm_num)
  set V₃ := V'.map W₀.subtype with hV₃
  have hV₃W : V₃ ≤ W₀ := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hcard : Nat.card V₃ = 8 := by
    rw [hV₃, ← Nat.card_congr (V'.equivMapOfInjective _ W₀.subtype_injective).toEquiv, hV']
    norm_num
  have hcen : ∀ g ∈ K, g ∈ Subgroup.centralizer (V₃ : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun v hv => zK_comm (hWZ (hV₃W hv)) hg
  refine ⟨V₃, hV₃W, hcard, fun s hs => ?_, fun hle => hk (hle ⟨k.2, hcen _ k.2⟩)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have hsc := Subgroup.mem_centralizer_iff.1 (hcen s (hBK (hS.1 hs)))
  constructor
  · intro hv
    rw [show s * v * s⁻¹ = v by rw [← hsc v hv, mul_inv_cancel_right]]
    exact hv
  · intro hv
    have h1 := hsc _ hv
    have : v = s * v * s⁻¹ := by
      calc v = s⁻¹ * (s * v * s⁻¹) * s := by group
        _ = s⁻¹ * (s * (s * v * s⁻¹)) := by rw [mul_assoc, h1]
        _ = s * v * s⁻¹ := by group
    rw [this]
    exact hv

theorem kgg2_of_model (hM : G2RuModel P T W V x ns a) (hrange : ψ.range = P)
    (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K) (hB : IsG2Block B) {S W₀ : Subgroup G}
    (hS : IsSylowTwoOf S B) (hWU : W₀ ≤ blockU B) (hBW : B ≤ Subgroup.normalizer (W₀ : Set G))
    (hW : Nat.card W₀ = 64) :
    ∃ V₃ : Subgroup G, V₃ ≤ W₀ ∧ Nat.card V₃ = 8 ∧ S ≤ Subgroup.normalizer (V₃ : Set G) ∧
      ¬ K ⊓ Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (B : Set G) := by
  obtain ⟨g, hgP, hgU, hgS, h64⟩ := exists_conj_model hM hrange hker hBK hB hS.1 hS.2.1
  have hUZ := blockU_inf_zK_eq hker hBK hB h64
  obtain ⟨k, hk⟩ := exists_preimage hrange (P.mul_mem (P.mul_mem (P.inv_mem hgP) hM.x_mem) hgP)
  have hkB : (k : G) ∉ Subgroup.normalizer (B : Set G) := by
    intro hkN
    apply hM.x_not
    have h1 := map_mem_normalizer_img (ψ := ψ) (k := k) (normalizer_blockU hkN)
    rw [hk] at h1
    rw [← hgU, mem_normalizer_map_conj]
    exact h1
  rcases sup_blockZ_eq hB.1 hWU hBW with hcase | hcase
  · refine kgg2_of_le_zK hBK hS hW (fun w hw => ?_) hkB
    have : w ∈ blockZ B := hcase ▸ Subgroup.mem_sup_left hw
    rw [← hUZ] at this
    exact this.2
  have hWK : W₀ ≤ K := hWU.trans ((blockU_le B).trans hBK)
  have hWZ : W₀ ⊓ blockZ B = ⊥ := by
    have hN : blockZ B ≤ Subgroup.normalizer (W₀ : Set G) := fun z hz =>
      hBW (blockU_le B (blockZ_le_blockU B hz))
    have h1 := card_sup_mul_card_inf_le_normalizer hN
    rw [hcase, card_blockU hB, hW] at h1
    have hZ : 0 < Nat.card (blockZ B) := Nat.card_pos
    have h2 : Nat.card ↥(W₀ ⊓ blockZ B) = 1 := by
      have : 64 * Nat.card (blockZ B) * Nat.card ↥(W₀ ⊓ blockZ B) =
          64 * Nat.card (blockZ B) * 1 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    exact Subgroup.card_eq_one.1 h2
  have hW0Z : W₀ ⊓ zK K = ⊥ := by
    rw [eq_bot_iff, ← hWZ]
    intro w hw
    have : w ∈ blockU B ⊓ zK K := ⟨hWU hw.1, hw.2⟩
    rw [hUZ] at this
    exact ⟨hw.1, this⟩
  have himgW : img ψ W₀ = img ψ (blockU B) := Subgroup.eq_of_le_of_card_ge (img_mono ψ hWU)
    (by rw [h64, card_img_of_inf hker hWK hW0Z, hW])
  have hcomm := commutator_eq_of_inf hB hWU hBW hWZ hW
  have hlift : ∀ q ∈ P ⊓ Subgroup.normalizer (W : Set Q), ∀ k' : ↥K, ψ k' = g⁻¹ * q * g →
      (k' : G) ∈ Subgroup.normalizer (B : Set G) ∧
        (k' : G) ∈ Subgroup.normalizer (W₀ : Set G) := by
    intro q hq k' hk'
    obtain ⟨hk'B, hk'U⟩ := lift_model hM hrange hker hBK hB hgP hgU hq hk'
    exact ⟨hk'B, lift_normalizer_W hker hBK hWU hBW hcomm hk'B (himgW ▸ hk'U)⟩
  set Vb := V.map (MulAut.conj g⁻¹).toMonoidHom with hVb
  have hmemVb : ∀ {y : Q}, y ∈ Vb ↔ g * y * g⁻¹ ∈ V := by
    intro y
    rw [hVb, mem_map_conj, inv_inv]
  have hVbU : Vb ≤ img ψ W₀ := by
    intro y hy
    rw [himgW]
    have h1 : g * y * g⁻¹ ∈ W := hM.V_le (hmemVb.1 hy)
    rw [← hgU, mem_map_conj] at h1
    simpa [mul_assoc] using h1
  set V₃ : Subgroup G := W₀ ⊓ (Vb.comap ψ).map K.subtype with hV₃
  have hmemV₃ : ∀ {v : G}, v ∈ V₃ ↔ v ∈ W₀ ∧ ∃ hv : v ∈ K, ψ ⟨v, hv⟩ ∈ Vb := by
    intro v
    rw [hV₃, Subgroup.mem_inf]
    constructor
    · rintro ⟨hv, ⟨w, hw, rfl⟩⟩
      exact ⟨hv, w.2, hw⟩
    · rintro ⟨hv, hvK, hψ⟩
      exact ⟨hv, ⟨v, hvK⟩, hψ, rfl⟩
  have hV₃W : V₃ ≤ W₀ := inf_le_left
  have hV₃K : V₃ ≤ K := hV₃W.trans hWK
  have hinj : ∀ {u v : G} (hu : u ∈ W₀) (hv : v ∈ W₀),
      ψ ⟨u, hWK hu⟩ = ψ ⟨v, hWK hv⟩ → u = v := fun hu hv h =>
    eq_of_img_eq hker hW0Z hu hv (hWK hu) (hWK hv) h
  have himgV : img ψ V₃ = Vb := by
    apply le_antisymm
    · intro y hy
      obtain ⟨v, hv, hvK, rfl⟩ := exists_of_mem_img ψ hy
      obtain ⟨-, hvK', hψ⟩ := hmemV₃.1 hv
      exact hψ
    · intro y hy
      obtain ⟨w, hw, hwK, rfl⟩ := exists_of_mem_img ψ (hVbU hy)
      exact mem_img_of_mem ψ (hmemV₃.2 ⟨hw, hwK, hy⟩) hwK
  have hcardV : Nat.card V₃ = 8 := by
    have hV₃Z : V₃ ⊓ zK K = ⊥ := eq_bot_iff.2 fun v hv => by
      rw [← hW0Z]
      exact ⟨hV₃W hv.1, hv.2⟩
    rw [← card_img_of_inf hker hV₃K hV₃Z, himgV, hVb, card_map_conj, hM.card_V]
  have hnormV : ∀ k' : ↥K, (k' : G) ∈ Subgroup.normalizer (W₀ : Set G) →
      ψ k' ∈ Subgroup.normalizer (Vb : Set Q) →
        (k' : G) ∈ Subgroup.normalizer (V₃ : Set G) := by
    intro k' hk'W hk'V
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    obtain ⟨hvW, hvK, hψ⟩ := hmemV₃.1 hv
    refine hmemV₃.2 ⟨(Subgroup.mem_normalizer_iff.1 hk'W v).1 hvW,
      K.mul_mem (K.mul_mem k'.2 hvK) (K.inv_mem k'.2), ?_⟩
    have : ψ ⟨(k' : G) * v * (k' : G)⁻¹, K.mul_mem (K.mul_mem k'.2 hvK) (K.inv_mem k'.2)⟩ =
        ψ k' * ψ ⟨v, hvK⟩ * (ψ k')⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact (Subgroup.mem_normalizer_iff.1 hk'V _).1 hψ
  have hSV : S ≤ Subgroup.normalizer (V₃ : Set G) := by
    intro s hs
    have hsK : s ∈ K := hBK (hS.1 hs)
    refine hnormV ⟨s, hsK⟩ (hBW (hS.1 hs)) ?_
    rw [hVb, mem_normalizer_map_conj, inv_inv]
    refine hM.T_V _ (hgS ⟨ψ ⟨s, hsK⟩, mem_img_of_mem ψ hs hsK, rfl⟩) ?_
    rw [← hgU, mem_normalizer_map_conj]
    simpa [mul_assoc] using map_mem_normalizer_img (ψ := ψ) (k := ⟨s, hsK⟩)
      (le_normalizer_blockU B (hS.1 hs))
  have hkc : ∀ v (hv : v ∈ V₃), ψ k * ψ ⟨v, hV₃K hv⟩ = ψ ⟨v, hV₃K hv⟩ * ψ k := by
    intro v hv
    obtain ⟨-, hvK, hψ⟩ := hmemV₃.1 hv
    have h1 := hM.x_comm _ (hmemVb.1 hψ)
    rw [hk]
    calc g⁻¹ * x * g * ψ ⟨v, hvK⟩ = g⁻¹ * (x * (g * ψ ⟨v, hvK⟩ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * ψ ⟨v, hvK⟩ * g⁻¹) * x) * g := by rw [h1]
      _ = ψ ⟨v, hvK⟩ * (g⁻¹ * x * g) := by group
  have hcZ : ∀ v ∈ V₃, (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ zK K := by
    intro v hv
    have hvK := hV₃K hv
    have hmem : (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem k.2 hvK) (K.inv_mem k.2)) (K.inv_mem hvK)
    have h1 : ψ ⟨(k : G) * v * (k : G)⁻¹ * v⁻¹, hmem⟩ = 1 := by
      have e : (⟨(k : G) * v * (k : G)⁻¹ * v⁻¹, hmem⟩ : ↥K) =
          k * ⟨v, hvK⟩ * k⁻¹ * (⟨v, hvK⟩ : ↥K)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hkc v hv]
      group
    exact mem_zK_of_ker hker (k := ⟨_, hmem⟩) h1
  have hsq : ∀ v ∈ V₃, v * v = 1 := fun v hv => blockU_sq hB.1 (hWU (hV₃W hv))
  have hgen : ∀ n ∈ ns, ∀ ν : ↥K, ψ ν = g⁻¹ * n * g → ∀ v ∈ V₃,
      (k : G) * (v * ((ν : G)⁻¹ * v * ν)) = (v * ((ν : G)⁻¹ * v * ν)) * k := by
    intro n hn ν hν v hv
    obtain ⟨hnP, hnW, hnV, hnx⟩ := hM.n_mem n hn
    obtain ⟨hνB, hνW⟩ := hlift n ⟨hnP, hnW⟩ ν hν
    have hνV : (ν : G) ∈ Subgroup.normalizer (V₃ : Set G) := by
      refine hnormV ν hνW ?_
      rw [hν, hVb, mem_normalizer_map_conj, inv_inv]
      simpa [mul_assoc] using hnV
    have hv' : (ν : G)⁻¹ * v * ν ∈ V₃ := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hνV) v).1 hv
      simpa using this
    set m : ↥K := ν * k * ν⁻¹ * k⁻¹ with hm
    have hψm : ψ m = g⁻¹ * (n * x * n⁻¹ * x⁻¹) * g := by
      rw [hm, map_mul, map_mul, map_mul, map_inv, map_inv, hν, hk]
      group
    have hmq : n * x * n⁻¹ * x⁻¹ ∈ P ⊓ Subgroup.normalizer (W : Set Q) :=
      ⟨P.mul_mem (P.mul_mem (P.mul_mem hnP hM.x_mem) (P.inv_mem hnP)) (P.inv_mem hM.x_mem), hnx⟩
    obtain ⟨-, hmW⟩ := hlift _ hmq m hψm
    have hmc : ∀ u ∈ V₃, (m : G) * u * (m : G)⁻¹ = u := by
      intro u hu
      have huW := hV₃W hu
      have hmu : (m : G) * u * (m : G)⁻¹ ∈ W₀ := (Subgroup.mem_normalizer_iff.1 hmW u).1 huW
      refine hinj hmu huW ?_
      have e1 : ψ ⟨(m : G) * u * (m : G)⁻¹, hWK hmu⟩ = ψ m * ψ ⟨u, hWK huW⟩ * (ψ m)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e1]
      have hu' : ψ ⟨u, hWK huW⟩ ∈ Vb := by
        obtain ⟨-, huK, hψ⟩ := hmemV₃.1 hu
        exact hψ
      have hνVb : ψ ν ∈ Subgroup.normalizer (Vb : Set Q) := by
        rw [hν, hVb, mem_normalizer_map_conj, inv_inv]
        simpa [mul_assoc] using hnV
      have hkVb : ∀ y ∈ Vb, ψ k * y = y * ψ k := by
        intro y hy
        obtain ⟨w, hw, hwK, rfl⟩ := exists_of_mem_img ψ (himgV ▸ hy : y ∈ img ψ V₃)
        exact hkc w hw
      have hy1 : (ψ ν)⁻¹ * ψ ⟨u, hWK huW⟩ * ψ ν ∈ Vb := by
        have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hνVb) _).1 hu'
        simpa using this
      have hc1 := hkVb _ hy1
      have hc2 := hkVb _ hu'
      rw [hm, map_mul, map_mul, map_mul, map_inv, map_inv]
      calc ψ ν * ψ k * (ψ ν)⁻¹ * (ψ k)⁻¹ * ψ ⟨u, hWK huW⟩ *
            (ψ ν * ψ k * (ψ ν)⁻¹ * (ψ k)⁻¹)⁻¹ =
          ψ ν * ψ k * (ψ ν)⁻¹ * ((ψ k)⁻¹ * ψ ⟨u, hWK huW⟩ * ψ k) * ψ ν * (ψ k)⁻¹ *
            (ψ ν)⁻¹ := by group
        _ = ψ ν * ψ k * (ψ ν)⁻¹ * ψ ⟨u, hWK huW⟩ * ψ ν * (ψ k)⁻¹ * (ψ ν)⁻¹ := by
          rw [show (ψ k)⁻¹ * ψ ⟨u, hWK huW⟩ * ψ k = ψ ⟨u, hWK huW⟩ by
            rw [mul_assoc, ← hc2, inv_mul_cancel_left]]
        _ = ψ ν * (ψ k * ((ψ ν)⁻¹ * ψ ⟨u, hWK huW⟩ * ψ ν)) * (ψ k)⁻¹ * (ψ ν)⁻¹ := by group
        _ = ψ ν * (((ψ ν)⁻¹ * ψ ⟨u, hWK huW⟩ * ψ ν) * ψ k) * (ψ k)⁻¹ * (ψ ν)⁻¹ := by
          rw [hc1]
        _ = ψ ⟨u, hWK huW⟩ := by group
    set c := (k : G) * v * (k : G)⁻¹ * v⁻¹ with hc
    have hcz : c ∈ zK K := hcZ v hv
    set v' := (ν : G)⁻¹ * v * ν with hv'def
    have hcz' := hcZ v' hv'
    have hνk : (ν : G) * k * (ν : G)⁻¹ = (m : G) * k := by
      rw [hm]
      simp [mul_assoc]
    have hkv' : (k : G) * v' * (k : G)⁻¹ = c * v' := by
      have h1 : (ν : G) * ((k : G) * v' * (k : G)⁻¹) * (ν : G)⁻¹ =
          ((m : G) * k) * v * ((m : G) * k)⁻¹ := by
        rw [← hνk, hv'def]
        group
      have h2 : ((m : G) * k) * v * ((m : G) * k)⁻¹ = (m : G) * (c * v) * (m : G)⁻¹ := by
        rw [hc]
        group
      have h3 : (m : G) * (c * v) * (m : G)⁻¹ = c * v := by
        have hcm := zK_comm hcz m.2
        calc (m : G) * (c * v) * (m : G)⁻¹ = (m : G) * c * v * (m : G)⁻¹ := by group
          _ = c * ((m : G) * v * (m : G)⁻¹) := by rw [← hcm]; group
          _ = c * v := by rw [hmc v hv]
      have h4 : (k : G) * v' * (k : G)⁻¹ = (ν : G)⁻¹ * (c * v) * ν := by
        rw [← h3, ← h2, ← h1]
        group
      rw [h4]
      have hcν' : (ν : G)⁻¹ * c = c * (ν : G)⁻¹ := (zK_comm hcz (K.inv_mem ν.2)).symm
      rw [hv'def]
      calc (ν : G)⁻¹ * (c * v) * ν = ((ν : G)⁻¹ * c) * v * ν := by group
        _ = (c * (ν : G)⁻¹) * v * ν := by rw [hcν']
        _ = c * ((ν : G)⁻¹ * v * ν) := by group
    have hcc : c * c = 1 := by
      have hvv := hsq v hv
      have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
      have hcv : c * v = v * c := zK_comm hcz (hV₃K hv)
      set w := (k : G) * v * (k : G)⁻¹ with hw
      have hww : w * w = 1 := by
        calc w * w = (k : G) * (v * v) * (k : G)⁻¹ := by rw [hw]; group
          _ = 1 := by rw [hvv]; group
      have hcw : c = w * v := by rw [hc, hvinv]
      have h1 : w = v * w * v := by
        rw [hcw] at hcv
        calc w = w * v * v := by rw [mul_assoc, hvv, mul_one]
          _ = v * (w * v) := hcv
          _ = v * w * v := by group
      calc c * c = w * v * (w * v) := by rw [hcw]
        _ = w * (v * w * v) := by group
        _ = w * w := by rw [← h1]
        _ = 1 := hww
    calc (k : G) * (v * v') = ((k : G) * v * (k : G)⁻¹) * ((k : G) * v' * (k : G)⁻¹) * k := by
          group
      _ = (c * v) * (c * v') * k := by
          rw [hkv', show (k : G) * v * (k : G)⁻¹ = c * v by rw [hc]; group]
      _ = c * c * (v * v') * k := by
          rw [show c * v * (c * v') = c * (v * c) * v' by group, ← zK_comm hcz (hV₃K hv)]
          group
      _ = v * v' * k := by rw [hcc, one_mul]
  set K₀ := V₃ ⊓ Subgroup.centralizer ({(k : G)} : Set G) with hK₀
  have hK₀V : Vb ≤ img ψ K₀ := by
    have hgenVb : Vb ≤ Subgroup.closure {u | ∃ v ∈ Vb, ∃ n ∈ ns,
        u = v * ((g⁻¹ * n * g)⁻¹ * v * (g⁻¹ * n * g))} := by
      intro y hy
      have h1 := hM.n_gen (hmemVb.1 hy)
      have h2 : y ∈ (Subgroup.closure {u | ∃ v ∈ V, ∃ n ∈ ns, u = v * (n⁻¹ * v * n)}).map
          (MulAut.conj g⁻¹).toMonoidHom := by
        rw [mem_map_conj, inv_inv]
        exact h1
      rw [MonoidHom.map_closure] at h2
      refine (Subgroup.closure_mono ?_) h2
      rintro _ ⟨u, ⟨v, hv, n, hn, rfl⟩, rfl⟩
      refine ⟨g⁻¹ * v * g, ?_, n, hn, ?_⟩
      · rw [hmemVb]
        simpa [mul_assoc] using hv
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
    refine hgenVb.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨y, hy, n, hn, rfl⟩
    obtain ⟨v, hv, hvK, rfl⟩ := exists_of_mem_img ψ (himgV ▸ hy : y ∈ img ψ V₃)
    obtain ⟨hnP, -, -, -⟩ := hM.n_mem n hn
    obtain ⟨ν, hν⟩ := exists_preimage hrange (P.mul_mem (P.mul_mem (P.inv_mem hgP) hnP) hgP)
    have hνW := (hlift n ⟨hnP, (hM.n_mem n hn).2.1⟩ ν hν).2
    have hνV : (ν : G) ∈ Subgroup.normalizer (V₃ : Set G) := by
      refine hnormV ν hνW ?_
      rw [hν, hVb, mem_normalizer_map_conj, inv_inv]
      simpa [mul_assoc] using (hM.n_mem n hn).2.2.1
    have hv' : (ν : G)⁻¹ * v * ν ∈ V₃ := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hνV) v).1 hv
      simpa using this
    have huV : v * ((ν : G)⁻¹ * v * ν) ∈ K₀ := by
      refine ⟨V₃.mul_mem hv hv', Subgroup.mem_centralizer_iff.2 ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hgen n hn ν hν v hv
    have huK : v * ((ν : G)⁻¹ * v * ν) ∈ K :=
      K.mul_mem hvK (K.mul_mem (K.mul_mem (K.inv_mem ν.2) hvK) ν.2)
    have h1 : ψ ⟨v * ((ν : G)⁻¹ * v * ν), huK⟩ =
        ψ ⟨v, hvK⟩ * ((ψ ν)⁻¹ * ψ ⟨v, hvK⟩ * ψ ν) := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    have key : ψ ⟨v, hvK⟩ * ((g⁻¹ * n * g)⁻¹ * ψ ⟨v, hvK⟩ * (g⁻¹ * n * g)) =
        ψ ⟨v * ((ν : G)⁻¹ * v * ν), huK⟩ := by rw [h1, hν]
    rw [SetLike.mem_coe, key]
    exact mem_img_of_mem ψ huV huK
  have hK₀eq : V₃ ≤ K₀ := by
    intro v hv
    obtain ⟨-, hvK, hψ⟩ := hmemV₃.1 hv
    obtain ⟨w, hw, hwK, he⟩ := exists_of_mem_img ψ (hK₀V hψ)
    have hwv : w = v := hinj (hV₃W hw.1) (hV₃W hv) he
    rw [← hwv]
    exact hw
  refine ⟨V₃, hV₃W, hcardV, hSV, fun hle => hkB (hle ⟨k.2, ?_⟩)⟩
  show (k : G) ∈ Subgroup.centralizer (V₃ : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := Subgroup.mem_centralizer_iff.1 (hK₀eq hv).2 k rfl
  exact this.symm

end CFSG.Quasithin.H13.Ch4.G2Ru
