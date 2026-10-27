module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

namespace LRed6

open CFSG.Assembly.LowTwoRank

variable {V : Type*} [CommGroup V]

theorem exists_preimage {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) {W : Subgroup V} (hWU : W ≤ U) (hWZ : W ⊓ Z = ⊥) [Finite ↥W] :
    ∃ Wm : Subgroup D.Amb, Wm ≤ D.sec ∧ D.ker ≤ Wm ∧
      Nat.card ↥Wm = Nat.card ↥W * Nat.card ↥D.ker ∧
      (∀ γ : D.Gam, (∀ w ∈ W, ((π γ : ↥H) : MulAut V) w = w) → ∀ m ∈ Wm, D.act γ m * m⁻¹ ∈ D.ker) ∧
      (∀ γ : D.Gam, (∀ w ∈ W, ((π γ : ↥H) : MulAut V) w ∈ W) → ∀ m ∈ Wm, D.act γ m ∈ Wm) ∧
      (∀ γ : D.Gam, (∀ w ∈ W, ((π γ : ↥H) : MulAut V) w ∈ W) →
        (∀ w ∈ W, ((π γ : ↥H) : MulAut V) w = w → w = 1) →
        ∀ m ∈ Wm, D.act γ m * m⁻¹ ∈ D.ker → m ∈ D.ker) := by
  obtain ⟨-, hZU, hkersec, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  let Q := ↥D.sec ⧸ D.ker.subgroupOf D.sec
  let q : ↥D.sec →* Q := QuotientGroup.mk' (D.ker.subgroupOf D.sec)
  let f : ↥W →* Q := β.comp (Subgroup.inclusion hWU)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : β (Subgroup.inclusion hWU w) = 1 := hw
    have h2 : ((Subgroup.inclusion hWU w : ↥U) : V) ∈ Z := (hβk _).mp h1
    have h3 : (w : V) ∈ W ⊓ Z := ⟨w.2, h2⟩
    rw [hWZ, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  let Wsec : Subgroup ↥D.sec := f.range.comap q
  refine ⟨Wsec.map D.sec.subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, -, rfl⟩
    exact m.2
  · intro k hk
    refine ⟨⟨k, hkersec hk⟩, ?_, rfl⟩
    show q ⟨k, hkersec hk⟩ ∈ f.range
    have : q ⟨k, hkersec hk⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [this]
    exact f.range.one_mem
  ·
    have hinj : Function.Injective D.sec.subtype := Subtype.coe_injective
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective Wsec D.sec.subtype hinj).toEquiv]
    let q' : ↥Wsec →* Q := q.comp Wsec.subtype
    have hrange : q'.range = f.range := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        exact m.2
      · intro hy
        obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
        exact ⟨⟨m, hy⟩, rfl⟩
    have hkerc : Nat.card ↥q'.ker = Nat.card ↥D.ker := by
      have hk : q'.ker = (D.ker.subgroupOf D.sec).subgroupOf Wsec := by
        ext m
        simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro hm
          have hm' : (QuotientGroup.mk (m : ↥D.sec) : Q) = 1 := hm
          exact (QuotientGroup.eq_one_iff (m : ↥D.sec)).mp hm'
        · intro hm
          exact (QuotientGroup.eq_one_iff (m : ↥D.sec)).mpr hm
      have e1 : Nat.card ↥((D.ker.subgroupOf D.sec).subgroupOf Wsec) =
          Nat.card ↥(D.ker.subgroupOf D.sec) := by
        refine Nat.card_congr (Subgroup.subgroupOfEquivOfLe ?_).toEquiv
        intro m hm
        have hm1 : (m : ↥D.sec) ∈ D.ker.subgroupOf D.sec := hm
        show q (m : ↥D.sec) ∈ f.range
        have hq1 : q (m : ↥D.sec) = 1 := (QuotientGroup.eq_one_iff (m : ↥D.sec)).mpr hm1
        rw [hq1]
        exact f.range.one_mem
      have e2 : Nat.card ↥(D.ker.subgroupOf D.sec) = Nat.card ↥D.ker :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkersec).toEquiv
      rw [hk, e1, e2]
    have h1 := Subgroup.card_ker_mul_card_range q'
    rw [hkerc, hrange, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm] at h1
    rw [← h1, mul_comm]
  ·
    intro γ hγ m hm
    obtain ⟨m', hm', rfl⟩ := hm
    obtain ⟨w, hw⟩ := hm'
    have hu : ((π γ : ↥H) : MulAut V) ((Subgroup.inclusion hWU w : ↥U) : V) ∈ U :=
      hHU (π γ) _ (Subgroup.inclusion hWU w).2
    have hact : D.act γ (m' : D.Amb) ∈ D.sec := hsec γ _ m'.2
    have hw' : β (Subgroup.inclusion hWU w) = QuotientGroup.mk m' := hw
    have h1 := hβe γ (Subgroup.inclusion hWU w) m' hu hact hw'
    have h2 : (⟨((π γ : ↥H) : MulAut V) ((Subgroup.inclusion hWU w : ↥U) : V), hu⟩ : ↥U) =
        Subgroup.inclusion hWU w := Subtype.ext (hγ w w.2)
    rw [h2, hw'] at h1
    have h3 := QuotientGroup.eq.mp h1
    have h4 : (m' : D.Amb)⁻¹ * D.act γ (m' : D.Amb) ∈ D.ker := h3
    rw [mul_comm]
    exact h4
  ·
    intro γ hγ m hm
    obtain ⟨m', hm', rfl⟩ := hm
    obtain ⟨w, hw⟩ := hm'
    have hu : ((π γ : ↥H) : MulAut V) ((Subgroup.inclusion hWU w : ↥U) : V) ∈ U :=
      hHU (π γ) _ (Subgroup.inclusion hWU w).2
    have hact : D.act γ (m' : D.Amb) ∈ D.sec := hsec γ _ m'.2
    have hw' : β (Subgroup.inclusion hWU w) = QuotientGroup.mk m' := hw
    have h1 := hβe γ (Subgroup.inclusion hWU w) m' hu hact hw'
    refine ⟨⟨D.act γ (m' : D.Amb), hact⟩, ?_, rfl⟩
    show q ⟨D.act γ (m' : D.Amb), hact⟩ ∈ f.range
    refine ⟨⟨((π γ : ↥H) : MulAut V) (w : V), hγ w w.2⟩, ?_⟩
    show β (Subgroup.inclusion hWU ⟨((π γ : ↥H) : MulAut V) (w : V), hγ w w.2⟩) = _
    exact h1
  ·
    intro γ hγ hfree m hm hmk
    obtain ⟨m', hm', rfl⟩ := hm
    obtain ⟨w, hw⟩ := hm'
    have hu : ((π γ : ↥H) : MulAut V) ((Subgroup.inclusion hWU w : ↥U) : V) ∈ U :=
      hHU (π γ) _ (Subgroup.inclusion hWU w).2
    have hact : D.act γ (m' : D.Amb) ∈ D.sec := hsec γ _ m'.2
    have hw' : β (Subgroup.inclusion hWU w) = QuotientGroup.mk m' := hw
    have h1 := hβe γ (Subgroup.inclusion hWU w) m' hu hact hw'
    have hq : (QuotientGroup.mk ⟨D.act γ (m' : D.Amb), hact⟩ : Q) = QuotientGroup.mk m' := by
      rw [QuotientGroup.eq]
      show (D.act γ (m' : D.Amb))⁻¹ * (m' : D.Amb) ∈ D.ker
      have h13 := D.ker.inv_mem hmk
      rwa [mul_inv_rev, inv_inv, mul_comm] at h13
    rw [hq, ← hw'] at h1
    have h5 : β ((⟨((π γ : ↥H) : MulAut V) ((Subgroup.inclusion hWU w : ↥U) : V), hu⟩ : ↥U) *
        (Subgroup.inclusion hWU w)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h6 : ((π γ : ↥H) : MulAut V) (w : V) * (w : V)⁻¹ ∈ Z := (hβk _).mp h5
    have h7 : ((π γ : ↥H) : MulAut V) (w : V) * (w : V)⁻¹ ∈ W :=
      W.mul_mem (hγ w w.2) (W.inv_mem w.2)
    have h8 : ((π γ : ↥H) : MulAut V) (w : V) * (w : V)⁻¹ ∈ W ⊓ Z := ⟨h7, h6⟩
    rw [hWZ, Subgroup.mem_bot] at h8
    have h9 : ((π γ : ↥H) : MulAut V) (w : V) = (w : V) := mul_inv_eq_one.mp h8
    have h10 : (w : V) = 1 := hfree w w.2 h9
    have h11 : w = 1 := Subtype.ext h10
    rw [h11, map_one, map_one] at hw'
    have : (m' : D.Amb) ∈ D.ker := by
      have h12 : (QuotientGroup.mk m' : Q) = 1 := hw'.symm
      exact (QuotientGroup.eq_one_iff (m' : ↥D.sec)).mp h12
    exact this

end LRed6

end CFSG.Quasithin
