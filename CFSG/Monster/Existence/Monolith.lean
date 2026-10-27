module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.Monster.Existence

open Subgroup

variable {D : Type*} [Group D]

theorem conj_eq_inv_of_inf_centralizer_eq_bot {N : Subgroup D} [Finite N] {v : D}
    (hv : v * v = 1) (hvN : ∀ n ∈ N, v * n * v⁻¹ ∈ N) (hC : N ⊓ centralizer {v} = ⊥) {n : D}
    (hn : n ∈ N) : v * n * v⁻¹ = n⁻¹ := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  let f : N → N := fun m => ⟨(m : D)⁻¹ * (v * m * v⁻¹), N.mul_mem (N.inv_mem m.2) (hvN m m.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h : (a : D)⁻¹ * (v * a * v⁻¹) = (b : D)⁻¹ * (v * b * v⁻¹) := congrArg Subtype.val hab
    have hk : (b : D) * (a : D)⁻¹ = v * ((b : D) * (a : D)⁻¹) * v⁻¹ := by
      calc (b : D) * (a : D)⁻¹
          = (b : D) * ((a : D)⁻¹ * (v * a * v⁻¹)) * (v * a * v⁻¹)⁻¹ := by group
        _ = (b : D) * ((b : D)⁻¹ * (v * b * v⁻¹)) * (v * a * v⁻¹)⁻¹ := by rw [h]
        _ = v * ((b : D) * (a : D)⁻¹) * v⁻¹ := by group
    have hmem : (b : D) * (a : D)⁻¹ ∈ N ⊓ centralizer {v} := by
      refine ⟨N.mul_mem b.2 (N.inv_mem a.2), mem_centralizer_singleton_iff.2 ?_⟩
      calc (b : D) * (a : D)⁻¹ * v = v * ((b : D) * (a : D)⁻¹) * v⁻¹ * v := by rw [← hk]
        _ = v * ((b : D) * (a : D)⁻¹) := by group
    rw [hC, mem_bot, mul_inv_eq_one] at hmem
    exact Subtype.ext hmem.symm
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.1 hf) ⟨n, hn⟩
  have hnm : n = (m : D)⁻¹ * (v * m * v⁻¹) := (congrArg Subtype.val hm).symm
  rw [hnm, hvi]
  calc v * ((m : D)⁻¹ * (v * m * v)) * v = v * (m : D)⁻¹ * v * m * (v * v) := by group
    _ = v * (m : D)⁻¹ * v * m := by rw [hv, mul_one]
    _ = v⁻¹ * (m : D)⁻¹ * v⁻¹ * m := by rw [hvi]
    _ = ((m : D)⁻¹ * (v * m * v))⁻¹ := by group

theorem centralizer_conj_le {S : Subgroup D} {g w : D} (hg : g ∈ S)
    (hw : centralizer {w} ≤ S) : centralizer {g * w * g⁻¹} ≤ S := by
  intro n hn
  have hc : g⁻¹ * n * g ∈ centralizer {w} := by
    rw [mem_centralizer_singleton_iff] at hn ⊢
    calc g⁻¹ * n * g * w = g⁻¹ * (n * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * n) * g := by rw [hn]
      _ = w * (g⁻¹ * n * g) := by group
  have h := S.mul_mem (S.mul_mem hg (hw hc)) (S.inv_mem hg)
  rwa [show g * (g⁻¹ * n * g) * g⁻¹ = n by group] at h

theorem le_of_conj_mem [Finite D] {S : Subgroup D} [IsSimpleGroup S] {x τ : D} (hx : x * x = 1)
    (hτS : τ ∈ S) (hcyc : τ * (τ * x * τ⁻¹) * τ⁻¹ = x * (τ * x * τ⁻¹))
    (hC : centralizer {x} ≤ S) {N : Subgroup D} (hN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N)
    (hN1 : N ≠ ⊥) : S ≤ N := by
  have hxS : x ∈ S := hC (mem_centralizer_singleton_iff.2 rfl)
  set y := τ * x * τ⁻¹ with hy
  have hyS : y ∈ S := S.mul_mem (S.mul_mem hτS hxS) (S.inv_mem hτS)
  have hyy : y * y = 1 := by
    rw [hy, show τ * x * τ⁻¹ * (τ * x * τ⁻¹) = τ * (x * x) * τ⁻¹ by group, hx, mul_one,
      mul_inv_cancel]
  have hCy : centralizer {y} ≤ S := centralizer_conj_le hτS hC
  have hCxy : centralizer {x * y} ≤ S := hcyc ▸ centralizer_conj_le hτS hCy
  have hnorm : (N.subgroupOf S).Normal := ⟨fun n hn s => by
    rw [mem_subgroupOf] at hn ⊢
    exact hN s s.2 n hn⟩
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · exfalso
    apply hN1
    have hNS : ∀ n ∈ N, n ∈ S → n = 1 := fun n hn hs => by
      have h : (⟨n, hs⟩ : S) ∈ N.subgroupOf S := hn
      rw [hbot, mem_bot] at h
      exact congrArg Subtype.val h
    have hbotC : ∀ w : D, centralizer {w} ≤ S → N ⊓ centralizer {w} = ⊥ := fun w hw =>
      eq_bot_iff.2 fun n hn => (mem_bot).2 (hNS n hn.1 (hw hn.2))
    have inv_x : ∀ n ∈ N, x * n * x⁻¹ = n⁻¹ := fun n hn =>
      conj_eq_inv_of_inf_centralizer_eq_bot hx (hN x hxS) (hbotC x hC) hn
    have inv_y : ∀ n ∈ N, y * n * y⁻¹ = n⁻¹ := fun n hn =>
      conj_eq_inv_of_inf_centralizer_eq_bot hyy (hN y hyS) (hbotC y hCy) hn
    refine eq_bot_iff.2 fun n hn => ?_
    have h1 : x * y * n * (x * y)⁻¹ = n := by
      calc x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
        _ = x * n⁻¹ * x⁻¹ := by rw [inv_y n hn]
        _ = (x * n * x⁻¹)⁻¹ := by group
        _ = n := by rw [inv_x n hn, inv_inv]
    have hmem : n ∈ N ⊓ centralizer {x * y} := by
      refine ⟨hn, mem_centralizer_singleton_iff.2 ?_⟩
      calc n * (x * y) = x * y * n * (x * y)⁻¹ * (x * y) := by rw [h1]
        _ = x * y * n := by group
    rwa [hbotC (x * y) hCxy] at hmem
  · intro s hs
    have h : (⟨s, hs⟩ : S) ∈ N.subgroupOf S := by rw [htop]; exact mem_top _
    exact h

theorem cycle_of_fourGroup {V : Subgroup D} [IsElementaryAbelian 2 V] (hV4 : Nat.card V = 4)
    {x τ : D} (hxV : x ∈ V) (hx : x ≠ 1) (hτV : ∀ v ∈ V, τ * v * τ⁻¹ ∈ V)
    (hτfix : ∀ v ∈ V, v ≠ 1 → τ * v * τ⁻¹ ≠ v) :
    τ * (τ * x * τ⁻¹) * τ⁻¹ = x * (τ * x * τ⁻¹) := by
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) v hv
    rwa [pow_two] at this
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val
      (isMulCommutative_iff.1 (inferInstance : IsMulCommutative V) ⟨a, ha⟩ ⟨b, hb⟩)
  have hconj1 : ∀ g : D, g ≠ 1 → τ * g * τ⁻¹ ≠ 1 := fun g hg h => hg (by
    have := congrArg (fun k => τ⁻¹ * k * τ) h
    simpa [mul_assoc] using this)
  set y := τ * x * τ⁻¹ with hy
  set z := τ * y * τ⁻¹ with hz
  have hyV : y ∈ V := hτV x hxV
  have hzV : z ∈ V := hτV y hyV
  have hy1 : y ≠ 1 := hconj1 x hx
  have hz1 : z ≠ 1 := hconj1 y hy1
  have hyx : y ≠ x := hτfix x hxV hx
  have hzy : z ≠ y := hτfix y hyV hy1
  have hxy1 : x * y ≠ 1 := fun h => hyx (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (hsq x hxV)])
  have hzx : z ≠ x := by
    intro hzx
    apply hτfix (x * y) (V.mul_mem hxV hyV) hxy1
    calc τ * (x * y) * τ⁻¹ = (τ * x * τ⁻¹) * (τ * y * τ⁻¹) := by group
      _ = x * y := by rw [← hy, ← hz, hzx, hcomm y hyV x hxV]
  have hsub : ({1, x, y, z} : Set D) ⊆ V := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact hxV
    · exact hyV
    · exact hzV
  have hVn : (V : Set D).ncard = 4 := by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hV4]
  have hcard : (V : Set D).ncard ≤ ({1, x, y, z} : Set D).ncard := by
    rw [hVn, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hzy.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hyx.symm, hzx.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hx.symm, hy1.symm, hz1.symm⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard
    (Set.finite_of_ncard_pos (by rw [hVn]; norm_num))
  have hxyV : x * y ∈ ({1, x, y, z} : Set D) := heq ▸ V.mul_mem hxV hyV
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxyV
  rcases hxyV with h | h | h | h
  · exact absurd h hxy1
  · exact absurd (mul_eq_left.1 h) hy1
  · exact absurd (mul_eq_right.1 h) hx
  · exact h.symm

theorem cycled_four_group_simple_subgroup_monolith [Finite D] {S : Subgroup D} [IsSimpleGroup S]
    (hSnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) {V : Subgroup D} [IsElementaryAbelian 2 V]
    (hV4 : Nat.card V = 4) {x τ : D} (hxV : x ∈ V) (hx : x ≠ 1) (hτS : τ ∈ S)
    (hτV : ∀ v ∈ V, τ * v * τ⁻¹ ∈ V) (hτfix : ∀ v ∈ V, v ≠ 1 → τ * v * τ⁻¹ ≠ v)
    (hC : centralizer {x} ≤ S) :
    (∀ N : Subgroup D, N.Normal → N ≠ ⊥ → S ≤ N) ∧
    (∀ (H : Type*) [Group H] (f : D →* H), (∃ s ∈ S, f s ≠ 1) → Function.Injective f) ∧
    ((∃ P : Sylow 2 D, (P : Subgroup D) ≤ S ∧ Nat.card (center P) = 2) →
      ∃ A : Subgroup D, ∃ _ : A.Normal, A ≠ ⊥ ∧
        (∀ N : Subgroup D, N.Normal → N ≠ ⊥ → A ≤ N) ∧
        IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧ S ≤ A ∧
        centralizer (A : Set D) = ⊥ ∧ Odd A.index ∧
        Function.Injective (MulAut.conjNormal (H := A)) ∧
        ∀ a : A, MulAut.conjNormal (a : D) = MulAut.conj a) := by
  have hxx : x * x = 1 := by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) x hxV
    rwa [pow_two] at this
  have hcyc := cycle_of_fourGroup hV4 hxV hx hτV hτfix
  have hS1 : S ≠ ⊥ := by
    obtain ⟨a, ha, b, hb, hab⟩ := hSnab
    intro h
    rw [h, mem_bot] at ha
    exact hab (by rw [ha, one_mul, mul_one])
  have part1 : ∀ N : Subgroup D, N.Normal → N ≠ ⊥ → S ≤ N := fun N hN hN1 =>
    le_of_conj_mem hxx hτS hcyc hC (fun s _ n hn => hN.conj_mem n hn s) hN1
  refine ⟨part1, fun H _ f ⟨s, hs, hfs⟩ => ?_, fun ⟨P, hPS, _⟩ => ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hk
    exact hfs ((part1 f.ker inferInstance hk) hs)
  let A : Subgroup D := ⨅ N : {N : Subgroup D // N.Normal ∧ N ≠ ⊥}, (N : Subgroup D)
  have hSA : S ≤ A := le_iInf fun N => part1 N N.2.1 N.2.2
  have hAN : ∀ N : Subgroup D, N.Normal → N ≠ ⊥ → A ≤ N := fun N hN hN1 =>
    iInf_le (fun N : {N : Subgroup D // N.Normal ∧ N ≠ ⊥} => (N : Subgroup D)) ⟨N, hN, hN1⟩
  have hAn : A.Normal := ⟨fun a ha g => mem_iInf.2 fun N =>
    N.2.1.conj_mem a (mem_iInf.1 ha N) g⟩
  have hA1 : A ≠ ⊥ := fun h => hS1 (le_bot_iff.1 (h ▸ hSA))
  have hAnab : ∃ a b : A, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hSnab
    exact ⟨⟨a, hSA ha⟩, ⟨b, hSA hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hAsimple : IsSimpleGroup A := by
    have : Nontrivial A := (nontrivial_iff_ne_bot A).2 hA1
    refine ⟨fun K hK => ?_⟩
    by_cases hK1 : K = ⊥
    · exact Or.inl hK1
    right
    set K₀ := K.map A.subtype with hK₀
    have hconjK : ∀ b : D, S ≤ K₀.map (MulAut.conj b⁻¹).toMonoidHom := by
      intro b
      refine le_of_conj_mem hxx hτS hcyc hC ?_ ?_
      · rintro s hs _ ⟨k, ⟨k', hk', rfl⟩, rfl⟩
        have hbsb : b * s * b⁻¹ ∈ A := hAn.conj_mem s (hSA hs) b
        refine ⟨(b * s * b⁻¹) * k' * (b * s * b⁻¹)⁻¹, ⟨⟨_, hbsb⟩ * k' * (⟨_, hbsb⟩)⁻¹,
          hK.conj_mem k' hk' ⟨_, hbsb⟩, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
        group
      · intro h
        apply hK1
        rw [eq_bot_iff]
        intro k hk
        have hk' : (MulAut.conj b⁻¹).toMonoidHom (k : D) ∈ K₀.map (MulAut.conj b⁻¹).toMonoidHom :=
          ⟨k, ⟨k, hk, rfl⟩, rfl⟩
        rw [h, mem_bot] at hk'
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hk'
        have : (k : D) = 1 := by
          have := congrArg (fun g => b * g * b⁻¹) hk'
          simpa [mul_assoc] using this
        exact (mem_bot).2 (Subtype.ext this)
    have hScore : S ≤ K₀.normalCore := fun s hs b => by
      obtain ⟨k, hk, hks⟩ := hconjK b hs
      simp only [inv_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hks
      rw [← hks, show b * (b⁻¹ * k * b) * b⁻¹ = k by group]
      exact hk
    have hcore : A ≤ K₀ := (hAN _ inferInstance
      (fun h => hS1 (le_bot_iff.1 (h ▸ hScore)))).trans (normalCore_le _)
    rw [eq_top_iff]
    intro a _
    obtain ⟨k, hk, hka⟩ := hcore a.2
    rwa [show k = a from Subtype.ext hka] at hk
  have hcent : centralizer (A : Set D) = ⊥ := by
    by_contra h
    obtain ⟨a, ha, b, hb, hab⟩ := hSnab
    have hbC := part1 _ inferInstance h hb
    exact hab (mem_centralizer_iff.1 hbC a (hSA ha))
  refine ⟨A, hAn, hA1, hAN, hAsimple, hAnab, hSA, hcent, ?_, ?_, fun a => ?_⟩
  · have h1 := P.not_dvd_index
    have h2 : A.index ∣ (P : Subgroup D).index := index_dvd_of_le (hPS.trans hSA)
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => h1 (h.trans h2))
  · rw [injective_iff_map_eq_one]
    intro d hd
    have hdC : d ∈ centralizer (A : Set D) := by
      rw [mem_centralizer_iff]
      intro a ha
      have := congrArg (fun φ : MulAut A => (φ ⟨a, ha⟩ : D)) hd
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc a * d = d * a * d⁻¹ * d := by rw [this]
        _ = d * a := by group
    rw [hcent, mem_bot] at hdC
    exact hdC
  · exact MulEquiv.ext fun h => Subtype.ext (by simp [MulAut.conjNormal_apply])

theorem isSimpleGroup_of_cycle [Finite D] {S : Subgroup D} [IsSimpleGroup S] {x τ : D}
    (hx : x * x = 1) (hτS : τ ∈ S) (hcyc : τ * (τ * x * τ⁻¹) * τ⁻¹ = x * (τ * x * τ⁻¹))
    (hC : centralizer {x} ≤ S) (P : Sylow 2 D) (hPS : (P : Subgroup D) ≤ S)
    (hNP : normalizer ((P : Subgroup D) : Set D) ≤ S) : IsSimpleGroup D := by
  have hS1 : (S : Subgroup D) ≠ ⊥ := fun h => by
    have : Nontrivial S := inferInstance
    rw [nontrivial_iff_ne_bot] at this
    exact this h
  have : Nontrivial D := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hS1 (Subsingleton.elim _ _)
  refine ⟨fun N hN => ?_⟩
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  right
  have hSN := le_of_conj_mem hx hτS hcyc hC (fun s _ n hn => hN.conj_mem n hn s) hN1
  have hF := Sylow.normalizer_sup_eq_top' P (hPS.trans hSN)
  rw [eq_top_iff, ← hF]
  exact sup_le (hNP.trans hSN) le_rfl

theorem normalizer_le_centralizer_of_center {P : Subgroup D} {x : D} (hx : orderOf x = 2)
    (hZ : (center P).map P.subtype = zpowers x) : normalizer (P : Set D) ≤ centralizer {x} := by
  intro g hg
  have hxZ : x ∈ (center P).map P.subtype := hZ ▸ mem_zpowers x
  obtain ⟨p, hp, hpx⟩ := hxZ
  have hpx' : (p : D) = x := hpx
  have hgp : g * x * g⁻¹ ∈ (center P).map P.subtype := by
    have hmem : g * x * g⁻¹ ∈ P := (mem_normalizer_iff.1 hg x).1 (hpx' ▸ p.2)
    refine ⟨⟨_, hmem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro q
    apply Subtype.ext
    have hq : g⁻¹ * (q : D) * g ∈ P := by
      rw [mem_normalizer_iff.1 hg]
      simp [mul_assoc]
    have hc := congrArg Subtype.val ((mem_center_iff.1 hp) ⟨_, hq⟩)
    simp only [Subgroup.coe_mul, hpx'] at hc ⊢
    calc (q : D) * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * q := by group
  rw [hZ, mem_zpowers_iff] at hgp
  obtain ⟨k, hk⟩ := hgp
  rw [← zpow_mod_orderOf, hx] at hk
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero] at hk
    exfalso
    have : x = 1 := by
      have := congrArg (fun k => g⁻¹ * k * g) hk
      simpa [mul_assoc] using this.symm
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one] at hk
    rw [mem_centralizer_singleton_iff]
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [← hk]

end CFSG.Monster.Existence
