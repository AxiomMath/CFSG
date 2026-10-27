module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5f

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127

namespace S127.L5

private def cyc3 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

private def ew34 : ↥(evenWeight 5) :=
  ⟨![0, 0, 0, 1, 1], by rw [evenWeight, AddMonoidHom.mem_ker]; decide⟩

private def ew03 : ↥(evenWeight 5) :=
  ⟨![1, 0, 0, 1, 0], by rw [evenWeight, AddMonoidHom.mem_ker]; decide⟩

private theorem permWeight_cyc3 : permWeight 5 (cyc3 : Equiv.Perm (Fin 5)) ew34 = ew34 := by
  decide

private theorem permWeight_cyc3_sq :
    permWeight 5 ((cyc3 ^ 2 : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ew03 ≠ ew03 := by
  decide

private theorem mk_injective5 {x y : ↥(evenWeight 5)}
    (h : (QuotientAddGroup.mk x : AltHeart 5) = QuotientAddGroup.mk y) : x = y :=
  (altHeart_mk_bijective ⟨2, rfl⟩).1 h

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t : G}

theorem D127.false_of_altBlock5 (d : D127 G T L V t) {α : ↥(Lt L t) →* alternatingGroup (Fin 5)}
    (hα : IsAltBlockTypeWith (Lt L t) 5 α) (hVU : V = blockU (Lt L t)) : False := by
  classical
  obtain ⟨hαs, -, β, hβs, hβk, hβ⟩ := hα
  obtain ⟨F, _, _, hF4, hNS⟩ := d.nat
  obtain ⟨-, αn, -, hαnk, βn, -, hβnk, hβn⟩ := hNS
  have : CharP F 2 := FFC.charP_two_of_card_pow (n := 2) (by rw [hF4]; norm_num)
  have hZ : blockZ (Lt L t) = Vt L t := by
    apply le_antisymm
    · have e : blockZ (Lt L t) = V ⊓ Subgroup.centralizer (Lt L t : Set G) := by
        rw [hVU]
        rfl
      rw [e]
      exact d.inf_centralizer_le
    · refine le_inf (hVU ▸ d.vt_le) fun z hz => Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      exact (Subgroup.mem_centralizer_iff.mp (d.lt_le hl).2 z hz).symm
  have hUN : Lt L t ≤ Subgroup.normalizer (blockU (Lt L t) : Set G) := hVU ▸ d.lt_le_normalizer
  obtain ⟨l, hl⟩ := hαs cyc3
  obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (QuotientAddGroup.mk ew34))
  set w : ↥(blockU (Lt L t)) :=
    ⟨l * v * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hUN l.2) v).mp v.2⟩ with hw
  have h1 := hβ l v w rfl ew34 (by rw [hv]; rfl)
  rw [hl, permWeight_cyc3] at h1
  have hwv : β w = β v := by
    rw [hv, h1]
    rfl
  have hk : ((w * v⁻¹ : ↥(blockU (Lt L t))) : G) ∈ Vt L t := by
    have hk : w * v⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv, mul_inv_cancel]
    rwa [hβk, Subgroup.mem_subgroupOf, hZ] at hk
  have hvZ : (v : G) ∉ Vt L t := by
    intro hvt
    have hk : v ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf, hZ]
      exact hvt
    rw [MonoidHom.mem_ker, hv] at hk
    have h0 : (QuotientAddGroup.mk ew34 : AltHeart 5) = QuotientAddGroup.mk 0 := hk
    have := mk_injective5 h0
    rw [ew34] at this
    exact absurd (congrArg (fun x : ↥(evenWeight 5) => (x : Fin 5 → ZMod 2) 3) this) (by decide)
  set lB : ↥(L ⊓ Subgroup.centralizer (Vt L t : Set G)) := ⟨l, d.lt_le l.2⟩ with hlB
  have hvV : (v : G) ∈ V := hVU ▸ v.2
  have hwV : (w : G) ∈ V := hVU ▸ w.2
  have hn := hβn lB ⟨v, hvV⟩ ⟨w, hwV⟩ rfl
  have hwv' : βn ⟨w, hwV⟩ = βn ⟨v, hvV⟩ := by
    have hk' : (⟨w, hwV⟩ * ⟨v, hvV⟩⁻¹ : ↥V) ∈ βn.ker := by
      rw [hβnk, Subgroup.mem_subgroupOf]
      exact hk
    rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk'
  rw [hwv'] at hn
  have hne : Multiplicative.toAdd (βn ⟨v, hvV⟩) ≠ 0 := by
    intro h0
    apply hvZ
    have hk' : (⟨v, hvV⟩ : ↥V) ∈ βn.ker := MonoidHom.mem_ker.mpr h0
    rw [hβnk, Subgroup.mem_subgroupOf] at hk'
    exact hk'
  have hsq := sq_eq_one_of_mulVec_eq (αn lB) hne hn.symm
  have hl2 : lB ^ 2 ∈ αn.ker := by rw [MonoidHom.mem_ker, map_pow, hsq]
  rw [hαnk, Subgroup.mem_subgroupOf] at hl2
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (QuotientAddGroup.mk ew03))
  have hu2 : (u : G) = ((l ^ 2 : ↥(Lt L t)) : G) * u * ((l ^ 2 : ↥(Lt L t)) : G)⁻¹ := by
    have hc : (u : G) * (l : G) ^ 2 = (l : G) ^ 2 * u :=
      Subgroup.mem_centralizer_iff.mp hl2 u (hVU ▸ u.2)
    show (u : G) = (l : G) ^ 2 * u * ((l : G) ^ 2)⁻¹
    rw [← hc, mul_inv_cancel_right]
  have h2 := hβ (l ^ 2) u u hu2 ew03 (by rw [hu]; rfl)
  rw [map_pow, hl, hu] at h2
  exact permWeight_cyc3_sq (mk_injective5 h2)

end S127.L5

open S127.L5 in
theorem lemma12_7_5K41Case1_of (h71 : Setup1271) (h74 : Lemma12_7_4) : Lemma12_7_5K41Case1 := by
  intro G _ _ T L V t h ht h18 _ hM0 K h1
  have d := d127_of h71 h74 h ht h18
  obtain ⟨n, hn, hblk, hVU, -⟩ := h1
  rw [← hM0] at hblk hVU
  rcases hn with rfl | rfl
  · obtain ⟨-, α, hα⟩ := hblk
    exact d.false_of_altBlock5 hα hVU
  · obtain ⟨-, α, hαs, hαk, -⟩ := hblk
    have e := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv
    rw [hαk] at e
    have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      rfl
    have h60 : Nat.card (ModO2 (Lt L t)) = 60 := d.card_modO2
    have : (60 : ℕ) = 360 := h60.symm.trans (e.trans h360)
    norm_num at this

end CFSG.Quasithin.H13
