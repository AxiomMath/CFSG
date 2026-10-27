module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitCount

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu
open scoped Matrix

variable {V : Type*} [CommGroup V]

theorem card_alt6_eq : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem hatA6_index_not_small {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 1080)
    (hperf : commutator G = ⊤) (hZ : Nat.card (Subgroup.center G) = 3)
    (e : G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 6)) (L : Subgroup G)
    (h2 : 2 ≤ L.index) (h5 : L.index ≤ 5) : False := by
  let φ := MulAction.toPermHom G (G ⧸ L)
  have hNL : φ.ker ≤ L := by
    intro g hg
    have h1 : φ g = 1 := hg
    have h2 : g • (QuotientGroup.mk 1 : G ⧸ L) = QuotientGroup.mk 1 := by
      have := congrArg (fun σ : Equiv.Perm (G ⧸ L) => σ (QuotientGroup.mk 1)) h1
      exact this
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at h2
    exact (L.inv_mem_iff).1 h2
  have hN1 : φ.ker.index ≤ 120 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (Equiv.Perm (G ⧸ L)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = (L.index).factorial := by rw [Nat.card_perm, ← Subgroup.index]
      _ ≤ 120 := by
          have : (L.index).factorial ≤ (5 : ℕ).factorial := Nat.factorial_le h5
          exact this.trans (by decide)
  have hN2 : L.index ∣ φ.ker.index := Subgroup.index_dvd_of_le hNL
  have hN3 := φ.ker.index_mul_card
  rw [hG] at hN3
  let ψ : G →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hM : (φ.ker.map ψ).Normal := (MonoidHom.normal_ker φ).map ψ hψ
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero (by intro h0; rw [h0] at hN3; omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map ψ) with h | h
  · have hle : φ.ker ≤ Subgroup.center G := by
      intro g hg
      have h1 : ψ g = 1 := by
        have : ψ g ∈ φ.ker.map ψ := ⟨g, hg, rfl⟩
        rw [h] at this
        exact this
      have h2 : (QuotientGroup.mk' (Subgroup.center G)) g = 1 := by
        apply e.injective
        rw [map_one]
        exact h1
      exact (QuotientGroup.eq_one_iff g).1 h2
    have h3 : Nat.card φ.ker ≤ 3 := hZ ▸ Subgroup.card_le_of_le hle
    nlinarith
  · have h1 : Nat.card (φ.ker.map ψ) ≤ Nat.card φ.ker :=
      Nat.card_le_card_of_surjective
        (fun n : φ.ker => (⟨ψ n, ⟨n, n.2, rfl⟩⟩ : φ.ker.map ψ))
        (by rintro ⟨_, n, hn, rfl⟩; exact ⟨⟨n, hn⟩, rfl⟩)
    rw [h, Subgroup.card_top, card_alt6_eq] at h1
    have hle3 : φ.ker.index ≤ 3 := by nlinarith
    have hge2 : 2 ≤ φ.ker.index := le_trans h2 (Nat.le_of_dvd hpos hN2)
    have hprime : (φ.ker.index).Prime := by
      interval_cases h : φ.ker.index <;> norm_num
    have : Fact (Nat.card (G ⧸ φ.ker)).Prime := ⟨by rw [← Subgroup.index]; exact hprime⟩
    have : IsCyclic (G ⧸ φ.ker) := isCyclic_of_prime_card rfl
    have : IsMulCommutative (G ⧸ φ.ker) := ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
    have hcomm := Abelianization.commutator_subset_ker (QuotientGroup.mk' φ.ker)
    rw [hperf, QuotientGroup.ker_mk'] at hcomm
    have : φ.ker = ⊤ := top_le_iff.1 hcomm
    rw [this, Subgroup.index_top] at hge2
    omega

theorem card_sup_normal_of_inf_eq_bot {G : Type*} [Group G] [Finite G] (S N : Subgroup G) [N.Normal]
    (h : S ⊓ N = ⊥) : Nat.card ↥(S ⊔ N) = Nat.card S * Nat.card N := by
  have e := QuotientGroup.quotientInfEquivProdNormalQuotient S N
  have h1 : N.subgroupOf S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ S ⊓ N := ⟨x.2, Subgroup.mem_subgroupOf.1 hx⟩
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have h2 := Nat.card_congr e.toEquiv
  rw [h1] at h2
  have h3 : Nat.card (↥S ⧸ (⊥ : Subgroup ↥S)) = Nat.card S :=
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  have h4 := (N.subgroupOf (S ⊔ N)).card_eq_card_quotient_mul_card_subgroup
  have h5 : Nat.card ↥(N.subgroupOf (S ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h5, ← h2, h3] at h4
  exact h4

theorem mem_orbitIn_trans {H : Subgroup (MulAut V)} {u v w : V}
    (huv : v ∈ orbitIn H u) (hvw : w ∈ orbitIn H v) : w ∈ orbitIn H u := by
  obtain ⟨h, hh, rfl⟩ := huv
  obtain ⟨h', hh', rfl⟩ := hvw
  exact ⟨h' * h, H.mul_mem hh' hh, rfl⟩

theorem mem_orbitIn_symm {H : Subgroup (MulAut V)} {v w : V} (hvw : w ∈ orbitIn H v) :
    v ∈ orbitIn H w := by
  obtain ⟨h, hh, rfl⟩ := hvw
  exact ⟨h⁻¹, H.inv_mem hh, by simp⟩

theorem mem_orbitIn_self (H : Subgroup (MulAut V)) (v : V) : v ∈ orbitIn H v :=
  ⟨1, H.one_mem, rfl⟩

theorem hatA6_orbits [Finite V] (hV : Nat.card V = 64) {H : Subgroup (MulAut V)}
    (hperf : commutator ↥H = ⊤) (hZ : Nat.card (Subgroup.center ↥H) = 3)
    (e : ↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6))
    (hfpf : ∀ z ∈ Subgroup.center ↥H, z ≠ 1 → ∀ v : V, (z : MulAut V) v = v → v = 1) :
    ∃ f : V, f ≠ 1 ∧ ∀ v : V, v ≠ 1 →
      (v ∈ orbitIn H f → Nat.card (orbitIn H v) = 18) ∧
        (v ∉ orbitIn H f → Nat.card (orbitIn H v) = 45) := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have hH : Nat.card ↥H = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥H),
      Nat.card_congr e.toEquiv, card_alt6_eq, hZ]
  have : Fintype ↥(Subgroup.center ↥H) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.center ↥H)) 3
    (by rw [← Nat.card_eq_fintype_card, hZ])
  set z₀ : ↥H := (zc : ↥H) with hz₀def
  have hz₀Z : z₀ ∈ Subgroup.center ↥H := zc.2
  have hz₀3 : orderOf z₀ = 3 := by
    rw [← hzc]
    exact Subgroup.orderOf_coe zc
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₀3
    omega
  have hz₀2 : z₀ ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hz₀3] at this
    omega
  have hfz : ∀ w : V, (z₀ : MulAut V) w = w → w = 1 := hfpf z₀ hz₀Z hz₀1
  have hfz2 : ∀ w : V, (z₀ : MulAut V) ((z₀ : MulAut V) w) = w → w = 1 := by
    intro w hw
    apply hfpf _ (Subgroup.pow_mem _ hz₀Z 2) hz₀2 w
    rw [Subgroup.coe_pow, pow_two]
    exact hw
  have hcommV : ∀ g : ↥H, ∀ w : V,
      (g : MulAut V) ((z₀ : MulAut V) w) = (z₀ : MulAut V) ((g : MulAut V) w) := by
    intro g w
    have := congrArg (fun k : ↥H => (k : MulAut V) w) (Subgroup.mem_center_iff.1 hz₀Z g)
    simpa using this
  have hOz : ∀ v w : V, w ∈ orbitIn H v → (z₀ : MulAut V) w ∈ orbitIn H v := by
    rintro v _ ⟨h, hh, rfl⟩
    exact ⟨(z₀ : MulAut V) * h, H.mul_mem z₀.2 hh, rfl⟩
  have h3dvd : ∀ v : V, v ≠ 1 → Nat.card (orbitIn H v) % 3 = 0 := by
    intro v hv
    have h := card_orbitIn_modEq hz₀3 v
    have hempty : orbitIn H v ∩ (fixV (Subgroup.zpowers (z₀ : MulAut V)) : Set V) = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hw hwz
      exact ne_one_of_mem_orbitIn hv hw (hfz w (mem_fixV_zpowers.1 hwz))
    rw [hempty, Nat.card_coe_set_eq (∅ : Set V), Set.ncard_empty] at h
    exact h
  have hdvd : ∀ v : V, Nat.card (orbitIn H v) ∣ 1080 := by
    intro v
    rw [orbitIn_eq_orbit, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, ← hH]
    exact Subgroup.index_dvd_card _
  have hidx : ∀ v : V, (MulAction.stabilizer ↥H v).index = Nat.card (orbitIn H v) := by
    intro v
    rw [orbitIn_eq_orbit, Nat.card_coe_set_eq, MulAction.index_stabilizer]
  have hV63 := ncard_ne_one (V := V)
  rw [hV] at hV63
  have hle : ∀ v : V, v ≠ 1 → Nat.card (orbitIn H v) ≤ 63 := by
    intro v hv
    have hsub : orbitIn H v ⊆ {x | x ≠ 1} := fun x hx => ne_one_of_mem_orbitIn hv hx
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Nat.card_coe_set_eq]
    omega
  have hnot3 : ∀ v : V, Nat.card (orbitIn H v) ≠ 3 := by
    intro v h
    exact hatA6_index_not_small hH hperf hZ e (MulAction.stabilizer ↥H v)
      (by rw [hidx, h]; norm_num) (by rw [hidx, h]; norm_num)
  have hnot15 : ∀ v : V, v ≠ 1 → Nat.card (orbitIn H v) ≠ 15 := by
    intro v hv h
    set S := MulAction.stabilizer ↥H v
    have hSZ : S ⊓ Subgroup.center ↥H = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨hgS, hgZ⟩
      rw [Subgroup.mem_bot]
      by_contra hg1
      exact hv (hfpf g hgZ hg1 v (MulAction.mem_stabilizer_iff.1 hgS))
    have hcard := card_sup_normal_of_inf_eq_bot S (Subgroup.center ↥H) hSZ
    have hS := S.index_mul_card
    rw [hidx, h, hH] at hS
    have hL := (S ⊔ Subgroup.center ↥H).index_mul_card
    rw [hcard, hZ, hH] at hL
    exact hatA6_index_not_small hH hperf hZ e (S ⊔ Subgroup.center ↥H) (by nlinarith) (by nlinarith)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card (G := ↥H) 5
    (by rw [← Nat.card_eq_fintype_card, hH]; norm_num)
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  set F : Subgroup V := fixV (Subgroup.zpowers (s : MulAut V)) with hFdef
  have hF4 : Nat.card F = 4 := by
    have hs' : orderOf (s : MulAut V) = 5 := by
      rw [← hs]
      exact orderOf_injective H.subtype Subtype.val_injective s
    have h1 := card_fixV_modEq hs'
    have h2 := Subgroup.card_subgroup_dvd_card F
    have h3 := card_fixV_ne hs1
    rw [hV] at h1 h2 h3
    have hle := Nat.le_of_dvd (by norm_num) h2
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card F <;> omega
  have hFz : ∀ w ∈ F, (z₀ : MulAut V) w ∈ F := by
    intro w hw
    rw [hFdef, mem_fixV_zpowers] at hw ⊢
    rw [hcommV s w, hw]
  have hFnt : Nontrivial ↥F := by
    rw [← Finite.one_lt_card_iff_nontrivial, hF4]
    norm_num
  obtain ⟨⟨f, hfF⟩, hf1⟩ := exists_ne (1 : ↥F)
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hz₀f1 : (z₀ : MulAut V) f ≠ 1 := fun h =>
    hf1' ((z₀ : MulAut V).injective (h.trans (map_one _).symm))
  have hz₀f2 : (z₀ : MulAut V) ((z₀ : MulAut V) f) ≠ 1 := fun h =>
    hz₀f1 ((z₀ : MulAut V).injective (h.trans (map_one _).symm))
  have hd1 : f ≠ (z₀ : MulAut V) f := fun h => hf1' (hfz f h.symm)
  have hd2 : f ≠ (z₀ : MulAut V) ((z₀ : MulAut V) f) := fun h => hf1' (hfz2 f h.symm)
  have hd3 : (z₀ : MulAut V) f ≠ (z₀ : MulAut V) ((z₀ : MulAut V) f) := fun h =>
    hd1 ((z₀ : MulAut V).injective h)
  have hFset : (F : Set V) = {1, f, (z₀ : MulAut V) f, (z₀ : MulAut V) ((z₀ : MulAut V) f)} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact F.one_mem
      · exact hfF
      · exact hFz _ hfF
      · exact hFz _ (hFz _ hfF)
    · rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hF4,
        Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hd3]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hd1, hd2⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hf1'.symm, hz₀f1.symm, hz₀f2.symm⟩
    · exact Set.toFinite _
  have hOF : ∀ v : V, v ≠ 1 →
      (f ∈ orbitIn H v → (orbitIn H v ∩ (F : Set V)).ncard = 3) ∧
        (f ∉ orbitIn H v → orbitIn H v ∩ (F : Set V) = ∅) := by
    intro v hv
    constructor
    · intro hf
      have heq : orbitIn H v ∩ (F : Set V) =
          {f, (z₀ : MulAut V) f, (z₀ : MulAut V) ((z₀ : MulAut V) f)} := by
        ext x
        constructor
        · rintro ⟨hxO, hxF⟩
          rw [hFset] at hxF
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxF ⊢
          rcases hxF with rfl | h | h | h
          · exact absurd rfl (ne_one_of_mem_orbitIn hv hxO)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · intro hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact ⟨hf, hfF⟩
          · exact ⟨hOz v _ hf, hFz _ hfF⟩
          · exact ⟨hOz v _ (hOz v _ hf), hFz _ (hFz _ hfF)⟩
      rw [heq, Set.ncard_insert_of_notMem, Set.ncard_pair hd3]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hd1, hd2⟩
    · intro hf
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxO hxF
      rw [hFset] at hxF
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxF
      rcases hxF with rfl | rfl | h | h
      · exact ne_one_of_mem_orbitIn hv hxO rfl
      · exact hf hxO
      · apply hf
        have h1 := hOz v _ (hOz v _ hxO)
        rw [h] at h1
        have h3 : (z₀ : MulAut V) ((z₀ : MulAut V) ((z₀ : MulAut V) f)) = f := by
          have : ((z₀ ^ 3 : ↥H) : MulAut V) f = f := by rw [← hz₀3, pow_orderOf_eq_one]; rfl
          rw [Subgroup.coe_pow, pow_succ, pow_two] at this
          exact this
        rwa [h3] at h1
      · apply hf
        have h1 := hOz v _ hxO
        rw [h] at h1
        have h3 : (z₀ : MulAut V) ((z₀ : MulAut V) ((z₀ : MulAut V) f)) = f := by
          have : ((z₀ ^ 3 : ↥H) : MulAut V) f = f := by rw [← hz₀3, pow_orderOf_eq_one]; rfl
          rw [Subgroup.coe_pow, pow_succ, pow_two] at this
          exact this
        rwa [h3] at h1
  have h5 : ∀ v : V, Nat.card (orbitIn H v) % 5 =
      (orbitIn H v ∩ (F : Set V)).ncard % 5 := by
    intro v
    have h := card_orbitIn_modEq hs v
    rw [Nat.card_coe_set_eq (orbitIn H v ∩ _)] at h
    exact h
  have hOf : Nat.card (orbitIn H f) = 18 := by
    have h1 := (hOF f hf1').1 (mem_orbitIn_self H f)
    have h2 := h5 f
    rw [h1] at h2
    have h3 := h3dvd f hf1'
    have h4 := hdvd f
    have h6 := hle f hf1'
    have h7 := hnot3 f
    generalize Nat.card (orbitIn H f) = n at h2 h3 h4 h6 h7 ⊢
    interval_cases n <;> omega
  have hdisj : ∀ v : V, v ∉ orbitIn H f → Disjoint (orbitIn H f) (orbitIn H v) := by
    intro v hv
    rw [Set.disjoint_left]
    intro x hxf hxv
    exact hv (mem_orbitIn_trans hxf (mem_orbitIn_symm hxv))
  have hsub : ∀ v : V, v ≠ 1 → orbitIn H v ⊆ {x | x ≠ 1} :=
    fun v hv x hx => ne_one_of_mem_orbitIn hv hx
  have hother : ∀ v : V, v ≠ 1 → v ∉ orbitIn H f →
      Nat.card (orbitIn H v) = 15 ∨ Nat.card (orbitIn H v) = 30 ∨
        Nat.card (orbitIn H v) = 45 := by
    intro v hv hvf
    have h1 := (hOF v hv).2 (fun h => hvf (mem_orbitIn_symm h))
    have h2 := h5 v
    rw [h1, Set.ncard_empty] at h2
    have h3 := h3dvd v hv
    have h4 := hdvd v
    have h6 : Nat.card (orbitIn H f) + Nat.card (orbitIn H v) ≤ 63 := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← Set.ncard_union_eq (hdisj v hvf)]
      have := Set.ncard_le_ncard (Set.union_subset (hsub f hf1') (hsub v hv)) (Set.toFinite _)
      omega
    rw [hOf] at h6
    have h7 := hnot3 v
    generalize Nat.card (orbitIn H v) = n at h2 h3 h4 h6 h7 ⊢
    have h8 : n ≤ 45 := by omega
    interval_cases n <;> omega
  refine ⟨f, hf1', fun v hv => ⟨fun hvf => ?_, fun hvf => ?_⟩⟩
  · have : orbitIn H v = orbitIn H f := by
      ext x
      exact ⟨fun hx => mem_orbitIn_trans hvf hx,
        fun hx => mem_orbitIn_trans (mem_orbitIn_symm hvf) hx⟩
    rw [this, hOf]
  · rcases hother v hv hvf with h | h | h
    · exact absurd h (hnot15 v hv)
    · exfalso
      have hunion : (orbitIn H f ∪ orbitIn H v).ncard = 48 := by
        rw [Set.ncard_union_eq (hdisj v hvf), ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
          hOf, h]
      obtain ⟨w, hw1, hw⟩ : ∃ w, w ≠ 1 ∧ w ∉ orbitIn H f ∪ orbitIn H v := by
        by_contra hcon
        push Not at hcon
        have : {x : V | x ≠ 1} ⊆ orbitIn H f ∪ orbitIn H v := fun x hx => hcon x hx
        have := Set.ncard_le_ncard this (Set.toFinite _)
        omega
      have hwf : w ∉ orbitIn H f := fun h' => hw (Or.inl h')
      have hwv : w ∉ orbitIn H v := fun h' => hw (Or.inr h')
      have hdvw : Disjoint (orbitIn H v) (orbitIn H w) := by
        rw [Set.disjoint_left]
        intro x hxv hxw
        exact hwv (mem_orbitIn_trans hxv (mem_orbitIn_symm hxw))
      have h3 : (orbitIn H f ∪ orbitIn H v ∪ orbitIn H w).ncard ≤ 63 := by
        have := Set.ncard_le_ncard
          (Set.union_subset (Set.union_subset (hsub f hf1') (hsub v hv)) (hsub w hw1))
          (Set.toFinite _)
        omega
      rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hdisj w hwf, hdvw⟩), hunion,
        ← Nat.card_coe_set_eq] at h3
      rcases hother w hw1 hwf with h' | h' | h'
      · exact hnot15 w hw1 h'
      · omega
      · omega
    · exact h


theorem orbits_of_hatA6 [Finite V] (hV : Nat.card V = 64) {H : Subgroup (MulAut V)}
    (hperf : commutator ↥H = ⊤) (hZ : Nat.card (Subgroup.center ↥H) = 3)
    (e : ↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6))
    (hfpf : ∀ z ∈ Subgroup.center ↥H, z ≠ 1 → ∀ v : V, (z : MulAut V) v = v → v = 1) :
    OrbitLengthsIn H [18, 45] ∧ OrbitsSeparated H := by
  obtain ⟨f, hf1, hf⟩ := hatA6_orbits hV hperf hZ e hfpf
  refine ⟨fun v hv => ?_, fun v w hv hw hvw => ?_⟩
  · by_cases h : v ∈ orbitIn H f
    · rw [(hf v hv).1 h]
      simp
    · rw [(hf v hv).2 h]
      simp
  · by_cases h : v ∈ orbitIn H f
    · have h18 := (hf v hv).1 h
      have hwf : w ∈ orbitIn H f := by
        by_contra hw'
        rw [h18, (hf w hw).2 hw'] at hvw
        omega
      exact mem_orbitIn_trans (mem_orbitIn_symm h) hwf
    · have h45 := (hf v hv).2 h
      have hwf : w ∉ orbitIn H f := by
        intro hw'
        rw [h45, (hf w hw).1 hw'] at hvw
        omega
      have hdisj : Disjoint (orbitIn H f) (orbitIn H v) := by
        rw [Set.disjoint_left]
        intro x hxf hxv
        exact h (mem_orbitIn_trans hxf (mem_orbitIn_symm hxv))
      have hsub : orbitIn H f ∪ orbitIn H v ⊆ {x | x ≠ 1} :=
        Set.union_subset (fun x hx => ne_one_of_mem_orbitIn hf1 hx)
          (fun x hx => ne_one_of_mem_orbitIn hv hx)
      have hcard : (orbitIn H f ∪ orbitIn H v).ncard = 63 := by
        rw [Set.ncard_union_eq hdisj, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
          (hf f hf1).1 (mem_orbitIn_self H f), h45]
      have h63 := ncard_ne_one (V := V)
      rw [hV] at h63
      have heq : orbitIn H f ∪ orbitIn H v = {x | x ≠ 1} :=
        Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
      have hw' : w ∈ orbitIn H f ∪ orbitIn H v := heq ▸ hw
      rcases hw' with h' | h'
      · exact absurd h' hwf
      · exact h'

theorem map_center_mulEquiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') :
    (Subgroup.center G).map φ.toMonoidHom = Subgroup.center G' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    change φ g' * φ x = φ x * φ g'
    rw [← map_mul, ← map_mul, hx g']
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy (φ g)]

theorem orbitTripleA6Six : OrbitTripleA6Six := by
  intro V _ _ H hH
  obtain ⟨K, _, _, Γ₀, hK4, -, ⟨hq, hZ3, ⟨eA⟩⟩, hscal, hR⟩ := hH
  obtain ⟨π, β, hR⟩ := (realizes_iff _ H ⊤ ⊥).1 hR
  have hact : ∀ (γ : ↥Γ₀) (v : V) (m : ↥(FFModel.nat Γ₀).sec),
      coordOf β v = QuotientGroup.mk m →
        coordOf β (((π γ : ↥H) : MulAut V) v) = QuotientGroup.mk
          ⟨Multiplicative.ofAdd (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Multiplicative.toAdd (α := Fin 3 → K) m.1), Subgroup.mem_top _⟩ :=
    fun γ v m hv => coordOf_act hR γ v m hv
  have hmk_inj : ∀ a b : ↥(FFModel.nat Γ₀).sec,
      (QuotientGroup.mk a : ↥(FFModel.nat Γ₀).sec ⧸
        (FFModel.nat Γ₀).ker.subgroupOf (FFModel.nat Γ₀).sec) = QuotientGroup.mk b → a = b := by
    intro a b h
    have h1 : ((a⁻¹ * b : ↥(FFModel.nat Γ₀).sec) : (FFModel.nat Γ₀).Amb) = 1 :=
      Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h))
    exact inv_mul_eq_one.1 (Subtype.ext h1)
  have hfix : ∀ (γ : ↥Γ₀) (v : V), ((π γ : ↥H) : MulAut V) v = v →
      ∃ x : Fin 3 → K, (∀ m : ↥(FFModel.nat Γ₀).sec, coordOf β v = QuotientGroup.mk m →
        Multiplicative.toAdd (α := Fin 3 → K) m.1 = x) ∧
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x := by
    intro γ v hv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (coordOf β v)
    refine ⟨Multiplicative.toAdd (α := Fin 3 → K) m.1, fun m' hm' => ?_, ?_⟩
    · rw [hmk_inj _ _ (hm.trans hm')]
    · have h1 := hact γ v m hm.symm
      rw [hv, ← hm] at h1
      have h2 := congrArg (fun y : ↥(FFModel.nat Γ₀).sec =>
        Multiplicative.toAdd (α := Fin 3 → K) y.1) (hmk_inj _ _ h1)
      exact h2.symm
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro γ' hγ
    rw [Subgroup.mem_bot]
    obtain ⟨γ, rfl⟩ : ∃ γ : ↥Γ₀, γ = γ' := ⟨γ', rfl⟩
    have hγ1 : ∀ v : V, ((π γ : ↥H) : MulAut V) v = v := by
      intro v
      rw [MonoidHom.mem_ker.1 hγ]
      rfl
    have hmat : ∀ x : Fin 3 → K,
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x := by
      intro x
      obtain ⟨v, hv⟩ := coordOf_surjective hR
        (QuotientGroup.mk (⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩ :
          ↥(FFModel.nat Γ₀).sec))
      obtain ⟨y, hy, hyx⟩ := hfix γ v (hγ1 v)
      rw [← hy _ hv] at hyx
      exact hyx
    apply Subtype.ext
    apply Units.ext
    ext i j
    have := congrFun (hmat (Pi.single j 1)) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    change (Pi.single j (1 : K) : Fin 3 → K) i = (1 : Matrix (Fin 3) (Fin 3) K) i j
    rw [Matrix.one_apply, Pi.single_apply]
  let φ : ↥Γ₀ ≃* ↥H := MulEquiv.ofBijective π ⟨hπinj, hR.1⟩
  have hV : Nat.card V = 64 := by
    have h1 := card_eq_of_realizesBy hR
    have h2 : Nat.card ↥(FFModel.nat Γ₀).ker = 1 := Subgroup.card_bot
    have h3 : Nat.card ↥(FFModel.nat Γ₀).sec = 64 := by
      change Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) = 64
      rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hK4]
      norm_num
    rw [h2, mul_one, h3] at h1
    exact h1
  have hperf : commutator ↥H = ⊤ := by
    have h1 := hq.1.commutator_eq_top
    have h2 := congrArg (Subgroup.map φ.toMonoidHom) h1
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      (MonoidHom.range_eq_top (f := φ.toMonoidHom)).2 φ.surjective] at h2
    rw [commutator_def]
    exact h2
  have hcen := map_center_mulEquiv φ
  have hZ : Nat.card (Subgroup.center ↥H) = 3 := by
    rw [← hZ3]
    exact (Nat.card_congr (Subgroup.centerCongr φ).toEquiv).symm
  have e : ↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ φ hcen).symm.trans eA
  have hfpf : ∀ z ∈ Subgroup.center ↥H, z ≠ 1 → ∀ v : V, (z : MulAut V) v = v → v = 1 := by
    intro z hz hz1 v hv
    obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ Subgroup.center ↥Γ₀, φ.toMonoidHom γ = z := by
      rw [← hcen] at hz
      exact hz
    obtain ⟨c, hc⟩ := hscal γ hγ
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hz1
      have : γ = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [hc, one_smul]
        rfl
      rw [this, map_one]
    obtain ⟨x, hx, hγx⟩ := hfix γ v hv
    rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec] at hγx
    have hx0 : x = 0 := by
      have h1 : (c - 1) • x = 0 := by rw [sub_smul, hγx, one_smul, sub_self]
      exact (smul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hc1)
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (coordOf β v)
    have hm1 := hx m hm.symm
    rw [hx0] at hm1
    apply coordOf_injective hR
    rw [← hm, coordOf_one]
    have : m = 1 := Subtype.ext (Multiplicative.toAdd.injective hm1)
    rw [this]
    rfl
  exact orbits_of_hatA6 hV hperf hZ e hfpf

end CFSG.Quasithin.H13.Orbit
