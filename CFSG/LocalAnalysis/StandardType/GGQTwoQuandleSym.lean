module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.StandardType


@[expose] def ggTransp (k : ℕ) : Set (Equiv.Perm (Fin k)) :=
  {t | ∃ a b : Fin k, a ≠ b ∧ t = Equiv.swap a b}

private lemma ggQ2xK_card_eq_two_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (hs : s.card = 2) (ha : a ∈ s) : ∃ b, b ≠ a ∧ s = {a, b} := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs
  have ha' : a = p ∨ a = q := by simpa using ha
  rcases ha' with hap | haq
  · refine ⟨q, ?_, ?_⟩
    · intro h
      exact hpq (hap ▸ h).symm
    · rw [hap]
  · refine ⟨p, ?_, ?_⟩
    · intro h
      exact hpq (haq ▸ h)
    · rw [haq]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto

private lemma ggQ2xK_swap_eq_of_support_eq {k : ℕ} {f g : Equiv.Perm (Fin k)}
    (hf : f.IsSwap) (hg : g.IsSwap) (h : f.support = g.support) : f = g := by
  obtain ⟨a, b, hab, rfl⟩ := hf
  obtain ⟨c, d, hcd, rfl⟩ := hg
  rw [Equiv.Perm.support_swap hab, Equiv.Perm.support_swap hcd] at h
  have ha : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Finset (Fin k)) := by rw [← h]; simp
    simpa using this
  rcases ha with hac | had
  · have hbd : b = d := by
      have hb : b ∈ ({c, d} : Finset (Fin k)) := by rw [← h]; simp
      rcases (by simpa using hb : b = c ∨ b = d) with hbc | hbd
      · exact (hab (hbc.trans hac.symm).symm).elim
      · exact hbd
    rw [hac, hbd]
  · have hbc : b = c := by
      have hb : b ∈ ({c, d} : Finset (Fin k)) := by rw [← h]; simp
      rcases (by simpa using hb : b = c ∨ b = d) with hbc | hbd
      · exact hbc
      · exact (hab (hbd.trans had.symm).symm).elim
    rw [had, hbc, Equiv.swap_comm]

private lemma ggQ2xK_support_injOn {k : ℕ} (F : Finset (Equiv.Perm (Fin k)))
    (hswap : ∀ t ∈ F, t.IsSwap) :
    Set.InjOn Equiv.Perm.support (↑F : Set (Equiv.Perm (Fin k))) := by
  intro s hs t ht hst
  exact ggQ2xK_swap_eq_of_support_eq (hswap s hs) (hswap t ht) hst

private lemma ggQ2xK_noncomm_share {k : ℕ} {f g : Equiv.Perm (Fin k)}
    (h : f * g ≠ g * f) : ∃ x, f x ≠ x ∧ g x ≠ x := by
  have hnc : ¬ f.Disjoint g := fun hd => h (Equiv.Perm.Disjoint.commute hd)
  unfold Equiv.Perm.Disjoint at hnc
  simp only [not_forall, not_or] at hnc
  exact hnc

private lemma ggQ2xK_inter_family {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (h2 : ∀ x ∈ F, x.card = 2)
    (hint : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → (x ∩ y).Nonempty)
    (hcard : 4 ≤ F.card) : ∃ a, ∀ x ∈ F, a ∈ x := by
  have hne : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨x0, hx0F⟩ := hne
  obtain ⟨a, b, hab, hx0⟩ := Finset.card_eq_two.mp (h2 x0 hx0F)
  by_cases hall : ∀ x ∈ F, a ∈ x
  · exact ⟨a, hall⟩
  · push Not at hall
    obtain ⟨y, hyF, hay⟩ := hall
    have hyx0 : y ≠ x0 := by
      intro h
      rw [h] at hay
      rw [hx0] at hay
      simp at hay
    have hby : b ∈ y := by
      obtain ⟨m, hm⟩ := hint y hyF x0 hx0F hyx0
      rw [Finset.mem_inter] at hm
      have hmx0 : m ∈ x0 := hm.2
      rw [hx0] at hmx0
      rcases (by simpa using hmx0 : m = a ∨ m = b) with hma | hmb
      · exact absurd (hma ▸ hm.1) hay
      · exact hmb ▸ hm.1
    obtain ⟨c, hcb, hy⟩ := ggQ2xK_card_eq_two_of_mem (h2 y hyF) hby
    have hca : c ≠ a := by
      intro hca
      apply hay
      rw [hy]
      simp [hca]
    by_cases hallb : ∀ x ∈ F, b ∈ x
    · exact ⟨b, hallb⟩
    · push Not at hallb
      obtain ⟨z, hzF, hbz⟩ := hallb
      have hzx0 : z ≠ x0 := by
        intro h
        rw [h] at hbz
        rw [hx0] at hbz
        simp at hbz
      have haz : a ∈ z := by
        obtain ⟨m, hm⟩ := hint z hzF x0 hx0F hzx0
        rw [Finset.mem_inter] at hm
        have hmx0 : m ∈ x0 := hm.2
        rw [hx0] at hmx0
        rcases (by simpa using hmx0 : m = a ∨ m = b) with hma | hmb
        · exact hma ▸ hm.1
        · exact absurd (hmb ▸ hm.1) hbz
      obtain ⟨d, hda, hz⟩ := ggQ2xK_card_eq_two_of_mem (h2 z hzF) haz
      have hyz : y ≠ z := by
        intro h
        rw [h] at hby
        exact hbz hby
      have hba : b ≠ a := Ne.symm hab
      have hbd : b ≠ d := by
        intro h
        apply hbz
        rw [hz]
        simp [h]
      have hcd : c = d := by
        obtain ⟨m, hm⟩ := hint y hyF z hzF hyz
        rw [Finset.mem_inter] at hm
        have h1 : m = b ∨ m = c := by
          have : m ∈ ({b, c} : Finset α) := by rw [← hy]; exact hm.1
          simpa using this
        have h2' : m = a ∨ m = d := by
          have : m ∈ ({a, d} : Finset α) := by rw [← hz]; exact hm.2
          simpa using this
        rcases h1 with hmb | hmc
        · rcases h2' with hma | hmd
          · exact absurd (hmb ▸ hma) hba
          · exact absurd (hmb ▸ hmd) hbd
        · rcases h2' with hma | hmd
          · exact absurd (hmc ▸ hma) hca
          · exact hmc.symm.trans hmd
      have hsub : F ⊆ ({x0, y, z} : Finset (Finset α)) := by
        intro u huF
        by_cases hux0 : u = x0
        · rw [hux0]; simp
        by_cases huy : u = y
        · rw [huy]; simp
        by_cases huz : u = z
        · rw [huz]; simp
        exfalso
        have hor : a ∈ u ∨ b ∈ u := by
          obtain ⟨m, hm⟩ := hint u huF x0 hx0F hux0
          rw [Finset.mem_inter] at hm
          have hmx0 : m ∈ x0 := hm.2
          rw [hx0] at hmx0
          rcases (by simpa using hmx0 : m = a ∨ m = b) with hma | hmb
          · exact Or.inl (hma ▸ hm.1)
          · exact Or.inr (hmb ▸ hm.1)
        rcases hor with hau | hbu
        · obtain ⟨e, hea, hu⟩ := ggQ2xK_card_eq_two_of_mem (h2 u huF) hau
          obtain ⟨n, hn⟩ := hint u huF y hyF huy
          rw [Finset.mem_inter] at hn
          have hnu : n ∈ u := hn.1
          have hny : n ∈ y := hn.2
          rw [hu] at hnu
          rw [hy] at hny
          have hnu' : n = a ∨ n = e := by simpa using hnu
          have hny' : n = b ∨ n = c := by simpa using hny
          have hna : n ≠ a := by
            intro h
            rcases hny' with hnb | hnc
            · exact hab (h ▸ hnb)
            · exact hca (h ▸ hnc).symm
          have hebc : e = b ∨ e = c := by
            rcases hnu' with hna' | hne
            · exact absurd hna' hna
            · rw [hne] at hny'
              exact hny'
          rcases hebc with heb | hec
          · apply hux0
            rw [hu, heb, ← hx0]
          · apply huz
            rw [hu, hec, hcd, ← hz]
        · obtain ⟨e, hea, hu⟩ := ggQ2xK_card_eq_two_of_mem (h2 u huF) hbu
          obtain ⟨n, hn⟩ := hint u huF z hzF huz
          rw [Finset.mem_inter] at hn
          have hnu : n ∈ u := hn.1
          have hnz : n ∈ z := hn.2
          rw [hu] at hnu
          rw [hz] at hnz
          have hnu' : n = b ∨ n = e := by simpa using hnu
          have hnz' : n = a ∨ n = d := by simpa using hnz
          have hnb : n ≠ b := by
            intro h
            rcases hnz' with hna | hnd
            · exact hba (h ▸ hna)
            · exact hbd (h ▸ hnd)
          have heac : e = a ∨ e = c := by
            rcases hnu' with hnb' | hne
            · exact absurd hnb' hnb
            · rw [hne] at hnz'
              rw [← hcd] at hnz'
              exact hnz'
          rcases heac with hea' | hec
          · apply hux0
            rw [hu, hea']
            rw [Finset.pair_comm b a, ← hx0]
          · apply huy
            rw [hu, hec, ← hy]
      have hle3 : ({x0, y, z} : Finset (Finset α)).card ≤ 3 := by
        have h1 := Finset.card_insert_le x0 ({y, z} : Finset (Finset α))
        have h2'' := Finset.card_insert_le y ({z} : Finset (Finset α))
        have h3 : ({z} : Finset (Finset α)).card = 1 := Finset.card_singleton z
        omega
      have : F.card ≤ 3 := le_trans (Finset.card_le_card hsub) hle3
      exfalso
      omega

private lemma ggQ2xK_clique_common {k : ℕ} (F : Finset (Equiv.Perm (Fin k)))
    (hcard : 4 ≤ F.card)
    (hswap : ∀ t ∈ F, t.IsSwap)
    (hnc : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → s * t ≠ t * s) :
    ∃ v, ∀ t ∈ F, t v ≠ v := by
  have h2 : ∀ x ∈ F.image Equiv.Perm.support, x.card = 2 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact Equiv.Perm.card_support_eq_two.mpr (hswap t ht)
  have hint : ∀ x ∈ F.image Equiv.Perm.support, ∀ y ∈ F.image Equiv.Perm.support,
      x ≠ y → (x ∩ y).Nonempty := by
    intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hst : s ≠ t := by
      intro h
      exact hxy (by rw [h])
    obtain ⟨u, hu1, hu2⟩ := ggQ2xK_noncomm_share (hnc s hs t ht hst)
    refine ⟨u, ?_⟩
    rw [Finset.mem_inter, Equiv.Perm.mem_support, Equiv.Perm.mem_support]
    exact ⟨hu1, hu2⟩
  have hcard' : 4 ≤ (F.image Equiv.Perm.support).card := by
    rw [Finset.card_image_of_injOn (ggQ2xK_support_injOn F hswap)]
    exact hcard
  obtain ⟨v, hv⟩ := ggQ2xK_inter_family (F.image Equiv.Perm.support) h2 hint hcard'
  refine ⟨v, fun t ht => ?_⟩
  have : Equiv.Perm.support t ∈ F.image Equiv.Perm.support :=
    Finset.mem_image.mpr ⟨t, ht, rfl⟩
  exact Equiv.Perm.mem_support.mp (hv _ this)

private def ggQ2xK_star {k : ℕ} (v : Fin k) : Finset (Equiv.Perm (Fin k)) :=
  (Finset.univ.erase v).image (fun w => Equiv.swap v w)

private lemma ggQ2xK_mem_star {k : ℕ} {v : Fin k} {t : Equiv.Perm (Fin k)} :
    t ∈ ggQ2xK_star v ↔ ∃ w, w ≠ v ∧ t = Equiv.swap v w := by
  rw [ggQ2xK_star, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hwt⟩
    rw [Finset.mem_erase] at hw
    exact ⟨w, hw.1, hwt.symm⟩
  · rintro ⟨w, hwv, hwt⟩
    exact ⟨w, by rw [Finset.mem_erase]; exact ⟨hwv, Finset.mem_univ w⟩, hwt.symm⟩

private lemma ggQ2xK_star_card {k : ℕ} (v : Fin k) : (ggQ2xK_star v).card = k - 1 := by
  have hinj : Function.Injective (fun w : Fin k => Equiv.swap v w) := by
    intro a b h
    have := congrArg (fun e : Equiv.Perm (Fin k) => e v) h
    simpa [Equiv.swap_apply_left] using this
  rw [ggQ2xK_star, Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]

private lemma ggQ2xK_star_subset {k : ℕ} {v : Fin k} {t : Equiv.Perm (Fin k)}
    (ht : t ∈ ggQ2xK_star v) : t ∈ ggTransp k := by
  rw [ggQ2xK_mem_star] at ht
  obtain ⟨w, hw, ht⟩ := ht
  exact ⟨v, w, Ne.symm hw, ht⟩

private lemma ggQ2xK_star_moves {k : ℕ} {v : Fin k} {t : Equiv.Perm (Fin k)}
    (ht : t ∈ ggQ2xK_star v) : t v ≠ v := by
  rw [ggQ2xK_mem_star] at ht
  obtain ⟨w, hw, ht⟩ := ht
  rw [ht, Equiv.swap_apply_left]
  exact hw

private lemma ggQ2xK_star_noncomm {k : ℕ} {v : Fin k} {s t : Equiv.Perm (Fin k)}
    (hs : s ∈ ggQ2xK_star v) (ht : t ∈ ggQ2xK_star v) (hst : s ≠ t) :
    s * t ≠ t * s := by
  rw [ggQ2xK_mem_star] at hs ht
  obtain ⟨a, ha, hs⟩ := hs
  obtain ⟨b, hb, ht⟩ := ht
  have hab : a ≠ b := by
    intro h
    apply hst
    rw [hs, ht, h]
  intro h
  rw [hs, ht] at h
  have hv := congrArg (fun e : Equiv.Perm (Fin k) => e v) h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_left] at hv
  rw [Equiv.swap_apply_of_ne_of_ne hb (Ne.symm hab),
    Equiv.swap_apply_of_ne_of_ne ha hab] at hv
  exact hab hv.symm

private lemma ggQ2xK_exists_fresh {k : ℕ} (hk : 3 ≤ k) (u v : Fin k) :
    ∃ a : Fin k, a ≠ u ∧ a ≠ v := by
  have hcard : ({u, v} : Finset (Fin k)).card < (Finset.univ : Finset (Fin k)).card := by
    calc ({u, v} : Finset (Fin k)).card ≤ 2 := Finset.card_le_two
      _ < k := by omega
      _ = (Finset.univ : Finset (Fin k)).card := by rw [Finset.card_univ, Fintype.card_fin]
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨a, (by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha :
    a ≠ u ∧ a ≠ v)⟩

private lemma ggQ2xK_star_inj {k : ℕ} (hk : 3 ≤ k) {u v : Fin k}
    (h : ggQ2xK_star u = ggQ2xK_star v) : u = v := by
  by_contra huv
  obtain ⟨a, hau, hav⟩ := ggQ2xK_exists_fresh hk u v
  have hmem0 : Equiv.swap u a ∈ ggQ2xK_star u := by
    rw [ggQ2xK_mem_star]
    exact ⟨a, hau, rfl⟩
  have hmem : Equiv.swap u a ∈ ggQ2xK_star v := by rw [← h]; exact hmem0
  have hmv : Equiv.swap u a v ≠ v := ggQ2xK_star_moves hmem
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm huv) (Ne.symm hav)] at hmv
  exact hmv rfl

private lemma ggQ2xK_eq_swap_of_mem_stars {k : ℕ} {u v : Fin k}
    {t : Equiv.Perm (Fin k)} (hu : t ∈ ggQ2xK_star u) (hv : t ∈ ggQ2xK_star v)
    (huv : u ≠ v) : t = Equiv.swap u v := by
  rw [ggQ2xK_mem_star] at hu
  obtain ⟨p, hp, ht⟩ := hu
  have hmv : t v ≠ v := ggQ2xK_star_moves hv
  rw [ht] at hmv
  rw [Equiv.swap_apply_ne_self_iff] at hmv
  rcases hmv.2 with hvu | hvp
  · exact absurd hvu.symm huv
  · rw [ht, hvp]

private lemma ggQ2xK_commute_iff (k : ℕ) (π : Equiv.Perm (Fin k) → Equiv.Perm (Fin k))
    (hinj : Set.InjOn π (ggTransp k))
    (hπ : ∀ s ∈ ggTransp k, ∀ t ∈ ggTransp k, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    {s t : Equiv.Perm (Fin k)} (hs : s ∈ ggTransp k) (ht : t ∈ ggTransp k) :
    s * t = t * s ↔ π s * π t = π t * π s := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := ht
  have hconj : Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b)⁻¹ ∈ ggTransp k := by
    rw [← Equiv.swap_apply_apply]
    exact ⟨_, _, fun h => hcd ((Equiv.swap a b).injective h), rfl⟩
  constructor
  · intro hcomm
    have h1 : Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b)⁻¹ = Equiv.swap c d := by
      rw [hcomm]; group
    have h2 := hπ (Equiv.swap a b) ⟨a, b, hab, rfl⟩ (Equiv.swap c d) ⟨c, d, hcd, rfl⟩
    rw [h1] at h2
    have h3 : π (Equiv.swap c d) * π (Equiv.swap a b)
        = π (Equiv.swap a b) * π (Equiv.swap c d) := by
      nth_rewrite 1 [h2]
      group
    exact h3.symm
  · intro hcomm
    have h2 := hπ (Equiv.swap a b) ⟨a, b, hab, rfl⟩ (Equiv.swap c d) ⟨c, d, hcd, rfl⟩
    have h3 : π (Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b)⁻¹) =
        π (Equiv.swap c d) := by
      rw [h2, hcomm]; group
    have h4 : Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b)⁻¹ = Equiv.swap c d :=
      hinj hconj ⟨c, d, hcd, rfl⟩ h3
    have h5 : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
      nth_rewrite 2 [← h4]
      group
    exact h5

private lemma ggQ2xK_image_star (k : ℕ) (hk : 5 ≤ k)
    (π : Equiv.Perm (Fin k) → Equiv.Perm (Fin k))
    (hπT : ∀ t ∈ ggTransp k, π t ∈ ggTransp k)
    (hinj : Set.InjOn π (ggTransp k))
    (hπ : ∀ s ∈ ggTransp k, ∀ t ∈ ggTransp k, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    (v : Fin k) : ∃ w, (ggQ2xK_star v).image π = ggQ2xK_star w := by
  set F := (ggQ2xK_star v).image π with hF
  have hswap : ∀ t ∈ F, t.IsSwap := by
    intro t ht
    rw [hF, Finset.mem_image] at ht
    obtain ⟨s, hs, hst⟩ := ht
    rw [← hst]
    exact hπT s (ggQ2xK_star_subset hs)
  have hnc : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → s * t ≠ t * s := by
    intro s hs t ht hst
    rw [hF, Finset.mem_image] at hs ht
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨t', ht', rfl⟩ := ht
    have hst' : s' ≠ t' := fun h => hst (by rw [h])
    have hiff := ggQ2xK_commute_iff k π hinj hπ (ggQ2xK_star_subset hs')
      (ggQ2xK_star_subset ht')
    intro hcomm
    exact (ggQ2xK_star_noncomm hs' ht' hst') (hiff.mpr hcomm)
  have hcardF : F.card = k - 1 := by
    rw [hF, Finset.card_image_of_injOn (hinj.mono (fun x hx => ggQ2xK_star_subset hx))]
    exact ggQ2xK_star_card v
  have h4 : 4 ≤ F.card := by
    rw [hcardF]
    omega
  obtain ⟨w, hw⟩ := ggQ2xK_clique_common F h4 hswap hnc
  have hsub : F ⊆ ggQ2xK_star w := by
    intro t ht
    rw [ggQ2xK_mem_star]
    obtain ⟨p, q, hpq, ht'⟩ := hswap t ht
    have htw : t w ≠ w := hw t ht
    rw [ht'] at htw
    rw [Equiv.swap_apply_ne_self_iff] at htw
    rcases htw.2 with hwp | hwq
    · refine ⟨q, ?_, ?_⟩
      · rw [hwp]
        exact hpq.symm
      · rw [ht', hwp]
    · refine ⟨p, ?_, ?_⟩
      · rw [hwq]
        exact hpq
      · rw [ht', hwq, Equiv.swap_comm]
  have hEq : F = ggQ2xK_star w := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcardF, ggQ2xK_star_card]
  exact ⟨w, hEq⟩

theorem ggQ2_quandle_aut_sym (k : ℕ) (hk : 5 ≤ k) (π : Equiv.Perm (Fin k) → Equiv.Perm (Fin k))
    (hπT : ∀ t ∈ ggTransp k, π t ∈ ggTransp k) (hinj : Set.InjOn π (ggTransp k))
    (hπ : ∀ s ∈ ggTransp k, ∀ t ∈ ggTransp k, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    ∃ g : Equiv.Perm (Fin k), ∀ t ∈ ggTransp k, π t = g * t * g⁻¹ := by
  let σ : Fin k → Fin k := fun v => Classical.choose (ggQ2xK_image_star k hk π hπT hinj hπ v)
  have hσ : ∀ v, (ggQ2xK_star v).image π = ggQ2xK_star (σ v) := fun v =>
    Classical.choose_spec (ggQ2xK_image_star k hk π hπT hinj hπ v)
  have hσinj : Function.Injective σ := by
    intro u v huv
    apply ggQ2xK_star_inj (k := k) (by omega)
    have h1 : (ggQ2xK_star u).image π = (ggQ2xK_star v).image π := by
      rw [hσ u, hσ v, huv]
    apply Finset.Subset.antisymm
    · intro s hs
      have hs' : π s ∈ (ggQ2xK_star u).image π := Finset.mem_image.mpr ⟨s, hs, rfl⟩
      rw [h1] at hs'
      obtain ⟨y, hy, hyπ⟩ := Finset.mem_image.mp hs'
      have : y = s := hinj (ggQ2xK_star_subset hy) (ggQ2xK_star_subset hs) hyπ
      rwa [← this]
    · intro s hs
      have hs' : π s ∈ (ggQ2xK_star v).image π := Finset.mem_image.mpr ⟨s, hs, rfl⟩
      rw [← h1] at hs'
      obtain ⟨y, hy, hyπ⟩ := Finset.mem_image.mp hs'
      have : y = s := hinj (ggQ2xK_star_subset hy) (ggQ2xK_star_subset hs) hyπ
      rwa [← this]
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  let g : Equiv.Perm (Fin k) := Equiv.ofBijective σ ⟨hσinj, hσsurj⟩
  have hg : ∀ v, g v = σ v := fun v => Equiv.ofBijective_apply σ ⟨hσinj, hσsurj⟩ v
  refine ⟨g, fun t ht => ?_⟩
  obtain ⟨a, b, hab, rfl⟩ := ht
  have ha_mem : π (Equiv.swap a b) ∈ ggQ2xK_star (σ a) := by
    rw [← hσ a]
    exact Finset.mem_image.mpr
      ⟨Equiv.swap a b, by rw [ggQ2xK_mem_star]; exact ⟨b, Ne.symm hab, rfl⟩, rfl⟩
  have hb_mem : π (Equiv.swap a b) ∈ ggQ2xK_star (σ b) := by
    rw [← hσ b]
    exact Finset.mem_image.mpr
      ⟨Equiv.swap a b, by rw [ggQ2xK_mem_star]; exact ⟨a, hab, Equiv.swap_comm a b⟩, rfl⟩
  have hfinal : π (Equiv.swap a b) = Equiv.swap (σ a) (σ b) :=
    ggQ2xK_eq_swap_of_mem_stars ha_mem hb_mem (hσinj.ne hab)
  rw [hfinal, ← Equiv.swap_apply_apply, ← hg a, ← hg b]

end CFSG.StandardType

end
