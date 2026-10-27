module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2Loc
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2Abs

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

namespace G2Loc

variable {N G : Type} [Group N] [Group G] {P : Subgroup N} {z : N} {T Q Tp : Subgroup N}

theorem toData (L : G2Loc P z T Q Tp) {φ : ↥P →* G} (hφ : Function.Injective φ)
    (hrange : φ.range = Subgroup.centralizer ({φ ⟨z, L.z_mem_P⟩} : Set G))
    (hconj : ∀ w ∈ (Tp.subgroupOf P).map φ, w * w = 1 → w ≠ 1 →
      IsConj (φ ⟨z, L.z_mem_P⟩) w) :
    G2Data G (φ ⟨z, L.z_mem_P⟩) ((T.subgroupOf P).map φ) ((Q.subgroupOf P).map φ)
      ((Tp.subgroupOf P).map φ) := by
  have hTP : T ≤ P := L.T_syl.1
  have hQP : Q ≤ P := L.Q_le.trans hTP
  have hTpP : Tp ≤ P := L.Tp_le.trans hTP
  set z' : ↥P := ⟨z, L.z_mem_P⟩ with hz'
  have hz'1 : z' ≠ 1 := fun h => L.z_ne (congrArg Subtype.val h)
  have hz'2 : z' * z' = 1 := Subtype.ext L.z_sq
  have mem_img : ∀ {X : Subgroup N} {y : G},
      y ∈ (X.subgroupOf P).map φ ↔ ∃ p : ↥P, (p : N) ∈ X ∧ φ p = y := fun {X y} => by
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have img_mem : ∀ {X : Subgroup N} (p : ↥P), φ p ∈ (X.subgroupOf P).map φ ↔ (p : N) ∈ X := by
    intro X p
    rw [mem_img]
    exact ⟨fun ⟨p', hp', e⟩ => by rw [← hφ e]; exact hp', fun h => ⟨p, h, rfl⟩⟩
  have comm_iff : ∀ p q : ↥P, φ p * φ q = φ q * φ p ↔ (p : N) * q = q * p := fun p q => by
    rw [← map_mul, ← map_mul]
    exact ⟨fun h => congrArg Subtype.val (hφ h), fun h => congrArg φ (Subtype.ext h)⟩
  have inC : ∀ {h : G}, h ∈ Subgroup.centralizer ({φ z'} : Set G) → ∃ r : ↥P, φ r = h :=
      fun hh => by
    rw [← hrange] at hh
    exact hh
  have central : ∀ {X : Subgroup N}, X ≤ P → (∀ w ∈ X, (∀ t ∈ X, t * w = w * t) → w = 1 ∨ w = z) →
      ∀ w ∈ (X.subgroupOf P).map φ, (∀ t ∈ (X.subgroupOf P).map φ, t * w = w * t) →
        w = 1 ∨ w = φ z' := by
    intro X hX hZ w hw hc
    obtain ⟨p, hpX, rfl⟩ := mem_img.1 hw
    have hcp : ∀ t ∈ X, t * (p : N) = p * t := fun t ht =>
      (comm_iff ⟨t, hX ht⟩ p).1 (hc _ ((img_mem _).2 ht))
    rcases hZ p hpX hcp with h | h
    · exact Or.inl (by rw [show p = 1 from Subtype.ext h, map_one])
    · exact Or.inr (by rw [show p = z' from Subtype.ext h])
  have conjmap : ∀ r p : ↥P, φ r * φ p * (φ r)⁻¹ = φ (r * p * r⁻¹) := by
    intro r p
    rw [map_mul, map_mul, map_inv]
  have conjmap' : ∀ r p : ↥P, (φ r)⁻¹ * φ p * φ r = φ (r⁻¹ * p * r) := by
    intro r p
    rw [map_mul, map_mul, map_inv]
  refine
    { z_ne := fun h => hz'1 (hφ (h.trans (map_one φ).symm))
      z_sq := by rw [← map_mul, hz'2, map_one]
      T_syl := hrange ▸ isSylowTwoOf_map_subgroupOf φ hφ L.T_syl
      T_card := (card_map_subgroupOf φ hφ hTP).trans L.T_card
      T_Z := central hTP L.T_Z
      T_N := ?_
      Q_le := ?_
      Q_card := (card_map_subgroupOf φ hφ hQP).trans L.Q_card
      Q_norm := ?_
      Q_comm := ?_
      Q_Z := central hQP L.Q_Z
      Q_nonab := ?_
      Tp_le := ?_
      Tp_card := ?_
      z_mem := (img_mem z').2 L.z_mem
      Tp_norm := ?_
      Tp_conj := hconj
      out_ex := ?_
      out_pair := ?_
      out_t := ?_ }
  · intro h hh h1 h2
    obtain ⟨r, rfl⟩ := inC hh
    refine (img_mem r).2 (L.T_N r r.2 (fun t ht => ?_) (fun t ht => ?_))
    · exact (img_mem (r * ⟨t, hTP ht⟩ * r⁻¹)).1 (by
        rw [← conjmap]; exact h1 _ ((img_mem _).2 ht))
    · exact (img_mem (r⁻¹ * ⟨t, hTP ht⟩ * r)).1 (by
        rw [← conjmap']; exact h2 _ ((img_mem _).2 ht))
  · intro y hy
    obtain ⟨p, hpQ, rfl⟩ := mem_img.1 hy
    exact (img_mem p).2 (L.Q_le hpQ)
  · intro h hh y hy
    obtain ⟨r, rfl⟩ := inC hh
    obtain ⟨p, hpQ, rfl⟩ := mem_img.1 hy
    rw [conjmap]
    exact (img_mem _).2 (L.Q_norm r r.2 p hpQ)
  · intro x hx y hy
    obtain ⟨p, hpQ, rfl⟩ := mem_img.1 hx
    obtain ⟨p', hpQ', rfl⟩ := mem_img.1 hy
    have e : φ p * φ p' * (φ p)⁻¹ * (φ p')⁻¹ = φ (p * p' * p⁻¹ * p'⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    rcases L.Q_comm p hpQ p' hpQ' with h | h
    · exact Or.inl (by rw [show p * p' * p⁻¹ * p'⁻¹ = 1 from Subtype.ext h, map_one])
    · exact Or.inr (by rw [show p * p' * p⁻¹ * p'⁻¹ = z' from Subtype.ext h])
  · obtain ⟨x, hx, y, hy, hxy⟩ := L.Q_nonab
    exact ⟨φ ⟨x, hQP hx⟩, (img_mem _).2 hx, φ ⟨y, hQP hy⟩, (img_mem _).2 hy,
      fun h => hxy ((comm_iff ⟨x, hQP hx⟩ ⟨y, hQP hy⟩).1 h)⟩
  · intro y hy
    obtain ⟨p, hpT, rfl⟩ := mem_img.1 hy
    exact (img_mem p).2 (L.Tp_le hpT)
  · rw [card_map_subgroupOf φ hφ hTP, card_map_subgroupOf φ hφ hTpP]
    exact L.Tp_card
  · intro h hh y hy
    obtain ⟨r, rfl⟩ := inC hh
    obtain ⟨p, hpQ, rfl⟩ := mem_img.1 hy
    rw [conjmap, img_mem, img_mem]
    exact L.Tp_norm r r.2 p hpQ
  · obtain ⟨v, hvQ, hvTp, hv2⟩ := L.out_ex
    refine ⟨φ ⟨v, hQP hvQ⟩, (img_mem _).2 hvQ, fun h => hvTp ((img_mem _).1 h), ?_⟩
    rw [← map_mul, show (⟨v, hQP hvQ⟩ : ↥P) * ⟨v, hQP hvQ⟩ = 1 from Subtype.ext hv2, map_one]
  · intro y hy hyTp hy2
    obtain ⟨p, hpQ, rfl⟩ := mem_img.1 hy
    have hpTp : (p : N) ∉ Tp := fun h => hyTp ((img_mem p).2 h)
    have hp2 : (p : N) * p = 1 := by
      have : φ (p * p) = φ 1 := by rw [map_mul, hy2, map_one]
      exact congrArg Subtype.val (hφ this)
    obtain ⟨a, haQ, b, hbQ, hav, hbv, hab⟩ := L.out_pair p hpQ hpTp hp2
    refine ⟨φ ⟨a, hQP haQ⟩, (img_mem _).2 haQ, φ ⟨b, hQP hbQ⟩, (img_mem _).2 hbQ,
      (comm_iff ⟨a, hQP haQ⟩ p).2 hav, (comm_iff ⟨b, hQP hbQ⟩ p).2 hbv, ?_⟩
    have e : φ ⟨a, hQP haQ⟩ * φ ⟨b, hQP hbQ⟩ * (φ ⟨a, hQP haQ⟩)⁻¹ * (φ ⟨b, hQP hbQ⟩)⁻¹ =
        φ (⟨a, hQP haQ⟩ * ⟨b, hQP hbQ⟩ * ⟨a, hQP haQ⟩⁻¹ * ⟨b, hQP hbQ⟩⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact congrArg φ (Subtype.ext hab)
  · intro y hy hyTp hy2
    obtain ⟨p, hpQ, rfl⟩ := mem_img.1 hy
    have hpTp : (p : N) ∉ Tp := fun h => hyTp ((img_mem p).2 h)
    have hp2 : (p : N) * p = 1 := by
      have : φ (p * p) = φ 1 := by rw [map_mul, hy2, map_one]
      exact congrArg Subtype.val (hφ this)
    obtain ⟨t, htT, h1, h2⟩ := L.out_t p hpQ hpTp hp2
    refine ⟨φ ⟨t, hTP htT⟩, (img_mem _).2 htT, ?_, ?_⟩
    · have e : φ ⟨t, hTP htT⟩ * φ p * (φ ⟨t, hTP htT⟩)⁻¹ * (φ p)⁻¹ =
          φ (⟨t, hTP htT⟩ * p * ⟨t, hTP htT⟩⁻¹ * p⁻¹) := by simp only [map_mul, map_inv]
      rw [e]
      intro h
      exact h1 (congrArg Subtype.val (hφ (h.trans (map_one φ).symm)))
    · have e : φ ⟨t, hTP htT⟩ * φ p * (φ ⟨t, hTP htT⟩)⁻¹ * (φ p)⁻¹ =
          φ (⟨t, hTP htT⟩ * p * ⟨t, hTP htT⟩⁻¹ * p⁻¹) := by simp only [map_mul, map_inv]
      rw [e]
      intro h
      exact h2 (congrArg Subtype.val (hφ h))

end G2Loc

end CFSG.Quasithin.H13.F431.G2Two
