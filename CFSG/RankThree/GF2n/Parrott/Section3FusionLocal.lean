module

public import CFSG.GH74.PartII.Lemma22E16Alt5
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.ThmCTBasic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.GH74.PartII CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG.OddStandard.ThmC
open CFSG.GH74.GLS.Bg.TwoGroups hiding IsElemAbelian

private abbrev vF : Finset (Equiv.Perm (Fin 5)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2}

set_option synthInstance.maxSize 4096 in
private theorem kleinFour_cases_aux : ∀ v : alternatingGroup (Fin 5),
    (v : Equiv.Perm (Fin 5)) ∈ vF → v ≠ 1 →
    ∀ w : alternatingGroup (Fin 5), (w : Equiv.Perm (Fin 5)) ∈ vF → w ≠ 1 →
      w = v ∨ w = cycle012A5 * v * cycle012A5⁻¹ ∨ w = cycle012A5⁻¹ * v * cycle012A5 := by
  decide +kernel

private theorem kleinFour_mem_of_commute_aux : ∀ v : alternatingGroup (Fin 5),
    (v : Equiv.Perm (Fin 5)) ∈ vF → v ≠ 1 →
    ∀ a : alternatingGroup (Fin 5), a * v = v * a → (a : Equiv.Perm (Fin 5)) ∈ vF := by
  decide +kernel

theorem kleinFourA5_conj_cases {v w : alternatingGroup (Fin 5)} (hv : v ∈ kleinFourA5)
    (hw : w ∈ kleinFourA5) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    w = v ∨ w = cycle012A5 * v * cycle012A5⁻¹ ∨ w = cycle012A5⁻¹ * v * cycle012A5 :=
  kleinFour_cases_aux v hv hv1 w hw hw1

theorem mem_kleinFourA5_of_commute {v a : alternatingGroup (Fin 5)} (hv : v ∈ kleinFourA5)
    (hv1 : v ≠ 1) (ha : a * v = v * a) : a ∈ kleinFourA5 :=
  kleinFour_mem_of_commute_aux v hv hv1 a ha

variable {K : Type} [Group K] [Finite K] {B D : Subgroup K}

def sylV (π : ↥B →* alternatingGroup (Fin 5)) : Subgroup K :=
  (kleinFourA5.comap π).map B.subtype

omit [Finite K] in
theorem mem_sylV {π : ↥B →* alternatingGroup (Fin 5)} {x : K} :
    x ∈ sylV π ↔ ∃ hx : x ∈ B, π ⟨x, hx⟩ ∈ kleinFourA5 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite K] in
theorem sylV_le (π : ↥B →* alternatingGroup (Fin 5)) : sylV π ≤ B :=
  fun _ hx => (mem_sylV.1 hx).1

omit [Finite K] in
theorem mem_iff_eq_one_of_ker {π : ↥B →* alternatingGroup (Fin 5)}
    (hk : π.ker = D.subgroupOf B) {x : K} (hx : x ∈ B) : x ∈ D ↔ π ⟨x, hx⟩ = 1 := by
  rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf]

omit [Finite K] in
theorem le_sylV (hDB : D ≤ B) {π : ↥B →* alternatingGroup (Fin 5)}
    (hk : π.ker = D.subgroupOf B) : D ≤ sylV π := by
  intro d hd
  refine mem_sylV.2 ⟨hDB hd, ?_⟩
  rw [(mem_iff_eq_one_of_ker hk (hDB hd)).1 hd]
  exact one_mem _

omit [Finite K] in
theorem conj_mem_of_ker (hDB : D ≤ B) {π : ↥B →* alternatingGroup (Fin 5)}
    (hk : π.ker = D.subgroupOf B) {g : K} (hg : g ∈ B) {d : K} (hd : d ∈ D) :
    g * d * g⁻¹ ∈ D := by
  have hd' : (⟨d, hDB hd⟩ : ↥B) ∈ π.ker := by rw [hk]; exact hd
  have := π.normal_ker.conj_mem _ hd' ⟨g, hg⟩
  rw [hk] at this
  exact this

omit [Finite K] in
theorem card_ker_of_eq (hDB : D ≤ B) (hD16 : Nat.card D = 16)
    {π : ↥B →* alternatingGroup (Fin 5)} (hk : π.ker = D.subgroupOf B) :
    Nat.card π.ker = 16 := by
  rw [hk]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv).trans hD16

omit [Finite K] in
private theorem ker_transitive {π : ↥B →* alternatingGroup (Fin 5)}
    (hk : π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b) :
    ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : ↥B, g * a * g⁻¹ = b := by
  intro a ha b hb ha1 hb1
  rw [hk, Subgroup.mem_subgroupOf] at ha hb
  obtain ⟨g, hg, hgab⟩ := hTrans a ha b hb (fun h => ha1 (Subtype.ext h))
    (fun h => hb1 (Subtype.ext h))
  exact ⟨⟨g, hg⟩, Subtype.ext hgab⟩

omit [Finite K] in
theorem card_sylV (hDB : D ≤ B) (hD16 : Nat.card D = 16) {π : ↥B →* alternatingGroup (Fin 5)}
    (hs : Function.Surjective π) (hk : π.ker = D.subgroupOf B) : Nat.card (sylV π) = 64 := by
  have hidx : (kleinFourA5.comap π).index = 15 := by
    rw [Subgroup.index_comap_of_surjective kleinFourA5 hs]
    have h := Subgroup.card_mul_index kleinFourA5
    rw [card_kleinFourA5, nat_card_alternatingGroup] at h
    simp only [Nat.card_fin] at h
    norm_num at h
    omega
  have h := Subgroup.card_mul_index (kleinFourA5.comap π)
  rw [hidx, card_eq_960_of_e16_alt5 hs (card_ker_of_eq hDB hD16 hk)] at h
  rw [sylV, Subgroup.card_map_of_injective B.subtype_injective]
  omega

theorem exists_mulEquiv_sylV (hDB : D ≤ B) (hD : IsElemAbelian 2 D) (hD16 : Nat.card D = 16)
    {π : ↥B →* alternatingGroup (Fin 5)} (hs : Function.Surjective π)
    (hk : π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b) :
    ∃ e : UT3 F4c ≃* ↥(sylV π), ∀ u, ((e u : ↥(sylV π)) : K) ∈ D ↔ u.b = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkcard := card_ker_of_eq hDB hD16 hk
  have hel : IsElemAbelian 2 π.ker := by
    rw [hk]
    exact hD.subgroupOf B
  let P₀ : Subgroup ↥B := kleinFourA5.comap π
  have hcard : Nat.card P₀ = 64 := by
    have h := card_sylV hDB hD16 hs hk
    rwa [sylV, Subgroup.card_map_of_injective B.subtype_injective] at h
  have hP0 : IsPGroup 2 P₀ := IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  have hidx : ¬ 2 ∣ P₀.index := by
    have h := Subgroup.card_mul_index P₀
    rw [hcard, card_eq_960_of_e16_alt5 hs hkcard] at h
    omega
  obtain ⟨e₁⟩ := nonempty_mulEquiv_sylSL3_4_of_e16_alt5 hs hel hkcard (ker_transitive hk hTrans)
    (hP0.toSylow hidx)
  have hco : ((hP0.toSylow hidx : Sylow 2 ↥B) : Subgroup ↥B) = P₀ :=
    IsPGroup.toSylow_coe hP0 hidx
  let e₀ : UT3 F4c ≃* ↥(sylV π) :=
    sylLCongr.symm.trans (e₁.symm.trans ((MulEquiv.subgroupCongr hco).trans
      (P₀.equivMapOfInjective B.subtype B.subtype_injective)))
  let E : Subgroup (UT3 F4c) := (D.subgroupOf (sylV π)).comap e₀.toMonoidHom
  have hmemE : ∀ u, u ∈ E ↔ ((e₀ u : ↥(sylV π)) : K) ∈ D := fun u => Iff.rfl
  have hDS := le_sylV hDB hk
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have h2 := hD.2 _ ((hmemE x).1 hx)
    apply e₀.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, map_one, Subgroup.coe_one, ← pow_two]
    exact h2
  have hcardE : Nat.card E = 16 := by
    rw [Nat.card_congr (e₀.toEquiv.subtypeEquiv (fun u => Iff.rfl) :
      ↥E ≃ ↥(D.subgroupOf (sylV π)))]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDS).toEquiv).trans hD16
  rcases T.eq_A_or_B hsq hcardE with hE | hE
  · refine ⟨e₀, fun u => ?_⟩
    rw [← hmemE, hE]
    exact T.mem_A
  · refine ⟨T.swap.trans e₀, fun u => ?_⟩
    change ((e₀ (T.swap u) : ↥(sylV π)) : K) ∈ D ↔ u.b = 0
    rw [← hmemE, hE]
    exact T.swap_mem_B_iff.trans T.mem_A

omit [Finite K] in
theorem exists_conj_eq_of_sylV (hDB : D ≤ B) (hD : CFSG.Open.IsElemAbelian 2 D)
    {π : ↥B →* alternatingGroup (Fin 5)} (hs : Function.Surjective π)
    (hk : π.ker = D.subgroupOf B) (e : UT3 F4c ≃* ↥(sylV π))
    (he : ∀ u, ((e u : ↥(sylV π)) : K) ∈ D ↔ u.b = 0)
    {u v : UT3 F4c} (hua : u.a = 0) (hub : u.b ≠ 0) (hva : v.a = 0) (hvb : v.b ≠ 0) :
    ∃ g ∈ B, g * ((e u : ↥(sylV π)) : K) * g⁻¹ = ((e v : ↥(sylV π)) : K) := by
  set ι : UT3 F4c → K := fun w => ((e w : ↥(sylV π)) : K) with hι
  have hιB : ∀ w, ι w ∈ B := fun w => sylV_le π (e w).2
  have hιmul : ∀ w w', ι (w * w') = ι w * ι w' := fun w w' => by
    simp only [hι, map_mul, Subgroup.coe_mul]
  have hιinv : ∀ w, ι w⁻¹ = (ι w)⁻¹ := fun w => by
    simp only [hι, map_inv, Subgroup.coe_inv]
  have hιinj : Function.Injective ι := fun w w' h => e.injective (Subtype.ext h)
  have hel : CFSG.Open.IsElemAbelian 2 π.ker := by
    rw [hk]
    exact hD.subgroupOf B
  obtain ⟨h, hπh, -⟩ := exists_pow_three_eq_one_of_e16_alt5 hs hel
  have hπV : ∀ w, π ⟨ι w, hιB w⟩ ∈ kleinFourA5 := fun w => (mem_sylV.1 (e w).2).2
  have hπ1 : ∀ w, w.b ≠ 0 → π ⟨ι w, hιB w⟩ ≠ 1 := fun w hw h1 =>
    hw ((he w).1 ((mem_iff_eq_one_of_ker hk (hιB w)).2 h1))
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : ↥B, π g₁ * π ⟨ι u, hιB u⟩ * (π g₁)⁻¹ = π ⟨ι v, hιB v⟩ := by
    rcases kleinFourA5_conj_cases (hπV u) (hπV v) (hπ1 u hub) (hπ1 v hvb) with h' | h' | h'
    · exact ⟨1, by rw [map_one, one_mul, inv_one, mul_one]; exact h'.symm⟩
    · exact ⟨h, by rw [hπh]; exact h'.symm⟩
    · exact ⟨h⁻¹, by rw [map_inv, hπh, inv_inv]; exact h'.symm⟩
  have hyB : (g₁ : K) * ι u * (g₁ : K)⁻¹ ∈ B := mul_mem (mul_mem g₁.2 (hιB u)) (inv_mem g₁.2)
  have hπy : π ⟨(g₁ : K) * ι u * (g₁ : K)⁻¹, hyB⟩ = π ⟨ι v, hιB v⟩ := by
    rw [show (⟨(g₁ : K) * ι u * (g₁ : K)⁻¹, hyB⟩ : ↥B) = g₁ * ⟨ι u, hιB u⟩ * g₁⁻¹ from rfl,
      map_mul, map_mul, map_inv, hg₁]
  have hyS : (g₁ : K) * ι u * (g₁ : K)⁻¹ ∈ sylV π := mem_sylV.2 ⟨hyB, hπy ▸ hπV v⟩
  set w := e.symm ⟨_, hyS⟩ with hw
  have hιw : ι w = (g₁ : K) * ι u * (g₁ : K)⁻¹ := by
    simp only [hι, hw, MulEquiv.apply_symm_apply]
  have hwb : w.b ≠ 0 := by
    intro hwb
    apply hub
    rw [← he u]
    have h1 : (g₁ : K)⁻¹ * ι w * (g₁ : K)⁻¹⁻¹ ∈ D :=
      conj_mem_of_ker hDB hk (inv_mem g₁.2) ((he w).2 hwb)
    rw [hιw, show (g₁ : K)⁻¹ * ((g₁ : K) * ι u * (g₁ : K)⁻¹) * (g₁ : K)⁻¹⁻¹ = ι u by group]
      at h1
    exact h1
  have hwsq : w * w = 1 := by
    apply hιinj
    rw [hιmul, hιw, show ι 1 = 1 by simp [hι]]
    have hu2 : ι u * ι u = 1 := by
      rw [← hιmul, T.sq_eq_one_of_mem_B (T.mem_B.2 hua)]
      simp [hι]
    calc (g₁ : K) * ι u * (g₁ : K)⁻¹ * ((g₁ : K) * ι u * (g₁ : K)⁻¹)
        = (g₁ : K) * (ι u * ι u) * (g₁ : K)⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hwa : w.a = 0 :=
    T.mem_B.1 (((T.sq_eq_one_iff_mem w).1 hwsq).resolve_left fun h => hwb (T.mem_A.1 h))
  have hzD : ι (w⁻¹ * v) ∈ D := by
    rw [mem_iff_eq_one_of_ker hk (hιB _)]
    rw [show (⟨ι (w⁻¹ * v), hιB _⟩ : ↥B) = (⟨ι w, hιB w⟩ : ↥B)⁻¹ * ⟨ι v, hιB v⟩ from
      Subtype.ext (by show ι (w⁻¹ * v) = (ι w)⁻¹ * ι v; rw [hιmul, hιinv]), map_mul, map_inv]
    rw [show (⟨ι w, hιB w⟩ : ↥B) = ⟨(g₁ : K) * ι u * (g₁ : K)⁻¹, hyB⟩ from Subtype.ext hιw,
      hπy, inv_mul_cancel]
  have hwZ : w ∉ Subgroup.center (UT3 F4c) := fun h => hwb ((T.mem_center_iff w).1 h).2
  have hzZ : w⁻¹ * v ∈ Subgroup.center (UT3 F4c) :=
    (T.mem_center_iff _).2 ⟨T.mem_B.1 (T.B.mul_mem (T.B.inv_mem (T.mem_B.2 hwa)) (T.mem_B.2 hva)),
      (he _).1 hzD⟩
  obtain ⟨d, hd⟩ := T.exists_conj_eq_mul hwZ hzZ
  refine ⟨ι d * g₁, mul_mem (hιB d) g₁.2, ?_⟩
  rw [mul_inv_cancel_left] at hd
  calc ι d * (g₁ : K) * ι u * (ι d * (g₁ : K))⁻¹
      = ι d * ((g₁ : K) * ι u * (g₁ : K)⁻¹) * (ι d)⁻¹ := by group
    _ = ι (d * w * d⁻¹) := by rw [← hιw, hιmul, hιmul, hιinv]
    _ = ι v := by rw [hd]

omit [Finite K] in
theorem mem_sylV_of_commute {π : ↥B →* alternatingGroup (Fin 5)}
    (hk : π.ker = D.subgroupOf B) {t : K} (ht : t ∈ sylV π) (htD : t ∉ D)
    {g : K} (hg : g ∈ B) (hc : g * t = t * g) : g ∈ sylV π := by
  obtain ⟨htB, hV⟩ := mem_sylV.1 ht
  have h1 : π ⟨t, htB⟩ ≠ 1 := fun h1 => htD ((mem_iff_eq_one_of_ker hk htB).2 h1)
  refine mem_sylV.2 ⟨hg, mem_kleinFourA5_of_commute hV h1 ?_⟩
  rw [← map_mul, ← map_mul]
  exact congrArg π (Subtype.ext hc)

theorem card_centralizer_eq_64 (hDB : D ≤ B) (hD16 : Nat.card D = 16)
    {π : ↥B →* alternatingGroup (Fin 5)} (hs : Function.Surjective π)
    (hk : π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set K) ≤ B)
    {d : K} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Nat.card (Subgroup.centralizer ({d} : Set K)) = 64 := by
  have hdker : (⟨d, hDB hd⟩ : ↥B) ∈ π.ker := by rw [hk]; exact hd
  have h64 := card_centralizer_eq_64_of_e16_alt5 hs (card_ker_of_eq hDB hD16 hk)
    (ker_transitive hk hTrans) hdker (fun h => hd1 (congrArg Subtype.val h))
  have heq : Subgroup.centralizer ({(⟨d, hDB hd⟩ : ↥B)} : Set ↥B) =
      (Subgroup.centralizer ({d} : Set K)).subgroupOf B := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [heq] at h64
  rw [← h64]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hCent d hd hd1)).toEquiv).symm

theorem mem_of_conj_mem (hD16 : Nat.card D = 16)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set K) ≤ B)
    {g : K} (hg : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : g ∈ B := by
  have : Nontrivial ↥D := Finite.one_lt_card_iff_nontrivial.1 (by rw [hD16]; norm_num)
  obtain ⟨⟨d₀, hd₀⟩, hd₀1⟩ := exists_ne (1 : ↥D)
  have hd₀1' : d₀ ≠ 1 := fun h => hd₀1 (Subtype.ext h)
  have hgd : g * d₀ * g⁻¹ ≠ 1 := by
    intro h
    apply hd₀1'
    calc d₀ = g⁻¹ * (g * d₀ * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨b, hb, hbd⟩ := hTrans d₀ hd₀ _ (hg d₀ hd₀) hd₀1' hgd
  have hc : b⁻¹ * g ∈ Subgroup.centralizer ({d₀} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * g * d₀ = b⁻¹ * (g * d₀ * g⁻¹) * g := by group
      _ = b⁻¹ * (b * d₀ * b⁻¹) * g := by rw [hbd]
      _ = d₀ * (b⁻¹ * g) := by group
  have := mul_mem hb (hCent d₀ hd₀ hd₀1' hc)
  simpa using this

theorem eq_top_of_normal_of_le (hDB : D ≤ B) (hD : CFSG.Open.IsElemAbelian 2 D)
    (hD16 : Nat.card D = 16) {π : ↥B →* alternatingGroup (Fin 5)} (hs : Function.Surjective π)
    (hk : π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set K) ≤ B)
    {L : Subgroup K} (hL : L.Normal) (hLB : L ≤ B) (hDL : D ≤ L) {t : K} (htL : t ∈ L)
    (htD : t ∉ D) : B = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hmapn : ((L.subgroupOf B).map π).Normal := (hL.subgroupOf B).map π hs
  have htop : (L.subgroupOf B).map π = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((L.subgroupOf B).map π) with h | h
    · exfalso
      have hmem : π ⟨t, hLB htL⟩ ∈ (L.subgroupOf B).map π := ⟨⟨t, hLB htL⟩, htL, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact htD ((mem_iff_eq_one_of_ker hk (hLB htL)).2 hmem)
    · exact h
  have hBL : B ≤ L := by
    intro b hb
    obtain ⟨l, hl, hlb⟩ : π ⟨b, hb⟩ ∈ (L.subgroupOf B).map π := by
      rw [htop]
      exact Subgroup.mem_top _
    have hker : (⟨b, hb⟩ * l⁻¹ : ↥B) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlb, mul_inv_cancel]
    rw [hk, Subgroup.mem_subgroupOf] at hker
    have := mul_mem (hDL hker) (Subgroup.mem_subgroupOf.1 hl)
    simpa using this
  have hBn : B.Normal := by
    rw [← le_antisymm hLB hBL]
    exact hL
  have hND : ∀ k : K, ∀ d ∈ D, k * d * k⁻¹ ∈ D := by
    intro k
    let D' : Subgroup K := D.map (MulAut.conj k).toMonoidHom
    have hmemD' : ∀ d ∈ D, k * d * k⁻¹ ∈ D' := fun d hd => ⟨d, hd, rfl⟩
    have hD'B : D' ≤ B := by
      rintro _ ⟨d, hd, rfl⟩
      exact hBn.conj_mem d (hDB hd) k
    have hD'n : (D'.subgroupOf B).Normal := by
      constructor
      intro x hx b
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_subgroupOf.1 hx
      rw [Subgroup.mem_subgroupOf]
      have hb' : k⁻¹ * (b : K) * k ∈ B := by
        simpa using hBn.conj_mem (b : K) b.2 k⁻¹
      refine ⟨(k⁻¹ * (b : K) * k) * d * (k⁻¹ * (b : K) * k)⁻¹,
        conj_mem_of_ker hDB hk hb' hd, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hdx ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hdx]
      group
    have hmap := hD'n.map π hs
    rcases Subgroup.Normal.eq_bot_or_eq_top ((D'.subgroupOf B).map π) with h | h
    · intro d hd
      have hx : k * d * k⁻¹ ∈ B := hD'B (hmemD' d hd)
      rw [mem_iff_eq_one_of_ker hk hx]
      have hmem : π ⟨k * d * k⁻¹, hx⟩ ∈ (D'.subgroupOf B).map π :=
        ⟨⟨k * d * k⁻¹, hx⟩, hmemD' d hd, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      obtain ⟨x, hx, hxc⟩ : cycle012A5 ∈ (D'.subgroupOf B).map π := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_subgroupOf.1 hx
      have hx2 : x * x = 1 := by
        apply Subtype.ext
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hdx
        rw [Subgroup.coe_mul, ← hdx, Subgroup.coe_one]
        have h2 : d * d = 1 := by rw [← pow_two]; exact hD.2 d hd
        calc k * d * k⁻¹ * (k * d * k⁻¹) = k * (d * d) * k⁻¹ := by group
          _ = 1 := by rw [h2]; group
      have hc2 : cycle012A5 * cycle012A5 = 1 := by rw [← hxc, ← map_mul, hx2, map_one]
      apply cycle012A5_ne_one
      calc cycle012A5 = cycle012A5 ^ 3 * (cycle012A5 * cycle012A5)⁻¹ := by group
        _ = 1 := by rw [cycle012A5_pow_three, hc2]; group
  rw [eq_top_iff]
  intro k _
  exact mem_of_conj_mem hD16 hTrans hCent (hND k)

end CFSG.RankThree.GF2n.Parrott
