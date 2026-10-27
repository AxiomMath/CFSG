module

public import CFSG.Quasithin.Vol2.Ch11SecBK10D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

namespace BK10

variable {G : Type} [Group G] [Finite G]

theorem not_isCoprimePrimeAut_of_pair {J S D : Subgroup G} {t : G} (hS2 : IsPGroup 2 S)
    (ht : t ∈ S) (htJ : t ∉ Subgroup.normalizer (J : Set G))
    (hSorb : ∀ s ∈ S, s ∈ Subgroup.normalizer (J : Set G) ∨
      t⁻¹ * s ∈ Subgroup.normalizer (J : Set G))
    (hJM : J ≤ Subgroup.normalizer
      ((J.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hJMK : ∀ z (hz : z ∈ J), z ∈ J.map (MulAut.conj t).toMonoidHom → piX J ⟨z, hz⟩ = 1)
    (hQ : IsSylowTwoOf (S ⊓ J) J)
    (hQ₀ : IsSylowTwoOf (S ⊓ (J ⊔ J.map (MulAut.conj t).toMonoidHom))
      (J ⊔ J.map (MulAut.conj t).toMonoidHom))
    (hD : Lin2.IsHallTwoPrimeOf D
      ((J ⊔ J.map (MulAut.conj t).toMonoidHom) ⊓ Subgroup.normalizer (S : Set G)))
    (hT : TorusRigid (XCls J)) {c : G} (hc : c ∈ Subgroup.normalizer (J : Set G))
    (hcM : c ∈ Subgroup.normalizer ((J.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hcD : ∀ d ∈ D, c * d * c⁻¹ = d) : ¬ IsCoprimePrimeAut (rhoX J ⟨c, hc⟩) := by
  set M := J.map (MulAut.conj t).toMonoidHom with hMdef
  have hmemM : ∀ x, x ∈ M ↔ t⁻¹ * x * t ∈ J := fun x => mem_map_conj_iff
  have hnorm : ∀ {n : G}, n ∈ Subgroup.normalizer (J : Set G) → ∀ x, x ∈ J ↔ n * x * n⁻¹ ∈ J :=
    fun hn x => Subgroup.mem_normalizer_iff.mp hn x
  have htt : t * t ∈ Subgroup.normalizer (J : Set G) := by
    rcases hSorb (t * t) (S.mul_mem ht ht) with h | h
    · exact h
    · exact absurd (by simpa using h) htJ
  have hmemM' : ∀ x, x ∈ M ↔ t * x * t⁻¹ ∈ J := by
    intro x
    rw [hmemM, hnorm htt]
    have h1 : t * t * (t⁻¹ * x * t) * (t * t)⁻¹ = t * x * t⁻¹ := by group
    rw [h1]
  have htJM : ∀ x ∈ J, t * x * t⁻¹ ∈ M := fun x hx => by
    rw [hmemM]
    simpa [mul_assoc] using hx
  have htMJ : ∀ x ∈ M, t * x * t⁻¹ ∈ J := fun x hx => (hmemM' x).mp hx
  have htiJM : ∀ x ∈ J, t⁻¹ * x * t⁻¹⁻¹ ∈ M := fun x hx => by
    rw [hmemM', inv_inv]
    simpa [mul_assoc] using hx
  have htiMJ : ∀ x ∈ M, t⁻¹ * x * t⁻¹⁻¹ ∈ J := fun x hx => by
    rw [inv_inv]
    exact (hmemM x).mp hx
  have hS₁t : ∀ s ∈ S, s ∈ Subgroup.normalizer (J : Set G) →
      t⁻¹ * s * t ∈ Subgroup.normalizer (J : Set G) := by
    intro s hs hsJ
    rcases hSorb _ (S.mul_mem (S.mul_mem (S.inv_mem ht) hs) ht) with h | h
    · exact h
    · exfalso
      apply htJ
      have h1 : t = s⁻¹ * ((t * t) * (t⁻¹ * (t⁻¹ * s * t))) := by group
      rw [h1]
      exact mul_mem (inv_mem hsJ) (mul_mem htt h)
  have hS₁M : ∀ s ∈ S, s ∈ Subgroup.normalizer (J : Set G) →
      s ∈ Subgroup.normalizer (M : Set G) := by
    intro s hs hsJ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemM, hmemM, hnorm (hS₁t s hs hsJ)]
    have h1 : t⁻¹ * s * t * (t⁻¹ * x * t) * (t⁻¹ * s * t)⁻¹ = t⁻¹ * (s * x * s⁻¹) * t := by group
    rw [h1]
  set J₀ := J ⊔ M with hJ₀
  set φ := projSup hJM hJMK with hφdef
  have htJ₀ : ∀ z ∈ J₀, t * z * t⁻¹ ∈ J₀ := fun z hz => conj_mem_sup_of_swap hJM htJM htMJ hz
  have htiJ₀ : ∀ z ∈ J₀, t⁻¹ * z * t ∈ J₀ := fun z hz => by
    have h1 := conj_mem_sup_of_swap hJM htiJM htiMJ hz
    rwa [inv_inv] at h1
  have hφc : ∀ x y (hx : x ∈ J₀) (hy : y ∈ J₀), x = y → φ ⟨x, hx⟩ = φ ⟨y, hy⟩ := by
    rintro x _ hx hy rfl
    rfl
  have hφmul : ∀ x y (hx : x ∈ J₀) (hy : y ∈ J₀),
      φ ⟨x * y, J₀.mul_mem hx hy⟩ = φ ⟨x, hx⟩ * φ ⟨y, hy⟩ := fun x y hx hy =>
    map_mul φ ⟨x, hx⟩ ⟨y, hy⟩
  have hφinv : ∀ x (hx : x ∈ J₀), φ ⟨x⁻¹, J₀.inv_mem hx⟩ = (φ ⟨x, hx⟩)⁻¹ := fun x hx =>
    map_inv φ ⟨x, hx⟩
  let τ : ↥J₀ →* ↥J₀ :=
    { toFun := fun z => ⟨t⁻¹ * z * t, htiJ₀ z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun z w => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  have hE1 : ∀ s ∈ S, ∀ hsJ : s ∈ Subgroup.normalizer (J : Set G), ∀ z (hz : z ∈ J₀)
      (h' : s * z * s⁻¹ ∈ J₀), φ ⟨s * z * s⁻¹, h'⟩ = rhoX J ⟨s, hsJ⟩ (φ ⟨z, hz⟩) :=
    fun s hs hsJ z hz h' => projSup_conj hJM hJMK hsJ (hS₁M s hs hsJ) ⟨z, hz⟩
  have hE2 : ∀ z (hz : z ∈ J₀) (h' : t * z * t⁻¹ ∈ J₀),
      φ ⟨t * z * t⁻¹, h'⟩ = rhoX J ⟨t * t, htt⟩ (φ ⟨t⁻¹ * z * t, htiJ₀ z hz⟩) := by
    intro z hz h'
    rw [← hE1 (t * t) (S.mul_mem ht ht) htt _ (htiJ₀ z hz)
      (conj_mem_sup hJM htt (hS₁M _ (S.mul_mem ht ht) htt) (htiJ₀ z hz))]
    exact hφc _ _ _ _ (by group)
  set P := (S.subgroupOf J).map (piX J) with hPdef
  have hP := isSylowTwoOf_map_piX hQ
  have hρP : ∀ s (hs : s ∈ S) (hsJ : s ∈ Subgroup.normalizer (J : Set G)), ∀ x ∈ P,
      rhoX J ⟨s, hsJ⟩ x ∈ P := by
    rintro s hs hsJ _ ⟨q, hq, rfl⟩
    rw [rhoX_piX]
    refine ⟨_, ?_, rfl⟩
    change s * (q : G) * s⁻¹ ∈ S
    exact S.mul_mem (S.mul_mem hs hq) (S.inv_mem hs)
  have hρP' : ∀ s (hs : s ∈ S) (hsJ : s ∈ Subgroup.normalizer (J : Set G)), ∀ x,
      x ∈ P ↔ rhoX J ⟨s, hsJ⟩ x ∈ P := by
    intro s hs hsJ x
    refine ⟨hρP s hs hsJ x, fun hx => ?_⟩
    have h1 := hρP s⁻¹ (S.inv_mem hs) (inv_mem hsJ) _ hx
    have h2 : rhoX J ⟨s⁻¹, inv_mem hsJ⟩ (rhoX J ⟨s, hsJ⟩ x) = x := by
      rw [← MulAut.mul_apply, ← map_mul]
      have h3 : (⟨s⁻¹, inv_mem hsJ⟩ : ↥(Subgroup.normalizer (J : Set G))) * ⟨s, hsJ⟩ = 1 :=
        Subtype.ext (inv_mul_cancel s)
      rw [h3, map_one, MulAut.one_apply]
    rwa [h2] at h1
  set S₁ := S ⊓ Subgroup.normalizer (J : Set G) with hS₁
  set Sh := (S₁.subgroupOf (Subgroup.normalizer (J : Set G))).map (rhoX J) with hSh
  have hSh2 : IsPGroup 2 Sh := by
    have h1 : IsPGroup 2 S₁ := hS2.to_le inf_le_left
    exact (IsPGroup.of_equiv h1 (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map _
  have hSP : ∀ p ∈ P, MulAut.conj p ∈ Sh := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← rhoX_of_mem J q.2]
    exact ⟨_, ⟨hq, Subgroup.le_normalizer q.2⟩, rfl⟩
  have hSs : ∀ s ∈ Sh, ∀ x, x ∈ P ↔ s x ∈ P := by
    rintro _ ⟨s, hs, rfl⟩ x
    exact hρP' s hs.1 hs.2 x
  obtain ⟨y, hyS, -, hyrig⟩ := hT P hP Sh hSh2 hSP hSs
  have hyρ : ∀ s ∈ S, ∀ hsJ : s ∈ Subgroup.normalizer (J : Set G),
      rhoX J ⟨s, hsJ⟩ y * y⁻¹ ∈ P := by
    intro s hs hsJ
    have h1 := hyS _ ⟨⟨s, hsJ⟩, ⟨hs, hsJ⟩, rfl⟩
    have h2 := P.inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  have hφJ : ∀ z (hz : z ∈ J), φ ⟨z, Subgroup.mem_sup_left hz⟩ = piX J ⟨z, hz⟩ :=
    fun z hz => projSup_of_mem hJM hJMK hz
  have hφQ : ∀ q ∈ S, ∀ hq : q ∈ J₀, φ ⟨q, hq⟩ ∈ P := by
    set P' := (S.subgroupOf J₀).map φ with hP'
    have hP'2 : IsPGroup 2 P' := by
      have h4 : IsPGroup 2 ((S ⊓ J₀).subgroupOf J₀) :=
        IsPGroup.of_equiv (hS2.to_le inf_le_left) (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      rw [Subgroup.inf_subgroupOf_right] at h4
      exact h4.map _
    have hPP' : P ≤ P' := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨⟨q, Subgroup.mem_sup_left q.2⟩, hq, hφJ q q.2⟩
    have hle := (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hP).2.2 P' le_top hP'2 hPP'
    intro q hq hqJ₀
    exact hle ⟨⟨q, hqJ₀⟩, hq, rfl⟩
  set R := ((P.comap φ) ⊓ (P.comap (φ.comp τ))).map J₀.subtype with hRdef
  have hRY : R ≤ J₀ := Subgroup.map_subtype_le _
  have hmemR : ∀ z (hz : z ∈ J₀), z ∈ R ↔
      φ ⟨z, hz⟩ ∈ P ∧ φ ⟨t⁻¹ * z * t, htiJ₀ z hz⟩ ∈ P := by
    intro z hz
    constructor
    · rintro ⟨z', ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨z, hz⟩, ⟨h1, h2⟩, rfl⟩
  have hφR : ∀ z (hz : z ∈ R), φ ⟨z, hRY hz⟩ ∈ P := fun z hz => ((hmemR z (hRY hz)).mp hz).1
  have hQR : S ⊓ J₀ ≤ R := by
    intro q hq
    rw [hmemR q hq.2]
    exact ⟨hφQ q hq.1 hq.2, hφQ _ (S.mul_mem (S.mul_mem (S.inv_mem ht) hq.1) ht) _⟩
  have hRs : ∀ s ∈ S, ∀ hsJ : s ∈ Subgroup.normalizer (J : Set G), ∀ z ∈ R,
      s * z * s⁻¹ ∈ R := by
    intro s hs hsJ z hz
    have hzJ₀ := hRY hz
    obtain ⟨h1, h2⟩ := (hmemR z hzJ₀).mp hz
    have hszJ₀ : s * z * s⁻¹ ∈ J₀ := conj_mem_sup hJM hsJ (hS₁M s hs hsJ) hzJ₀
    rw [hmemR _ hszJ₀]
    have hs' : t⁻¹ * s * t ∈ S := S.mul_mem (S.mul_mem (S.inv_mem ht) hs) ht
    have hs'J := hS₁t s hs hsJ
    have hs'z : (t⁻¹ * s * t) * (t⁻¹ * z * t) * (t⁻¹ * s * t)⁻¹ ∈ J₀ :=
      conj_mem_sup hJM hs'J (hS₁M _ hs' hs'J) (htiJ₀ z hzJ₀)
    constructor
    · rw [hE1 s hs hsJ z hzJ₀ hszJ₀]
      exact hρP s hs hsJ _ h1
    · rw [hφc (t⁻¹ * (s * z * s⁻¹) * t) _ _ hs'z (by group),
        hE1 _ hs' hs'J _ (htiJ₀ z hzJ₀) hs'z]
      exact hρP _ hs' hs'J _ h2
  have hRt : ∀ z ∈ R, t * z * t⁻¹ ∈ R := by
    intro z hz
    have hzJ₀ := hRY hz
    obtain ⟨h1, h2⟩ := (hmemR z hzJ₀).mp hz
    rw [hmemR _ (htJ₀ z hzJ₀)]
    constructor
    · rw [hE2 z hzJ₀ (htJ₀ z hzJ₀)]
      exact hρP (t * t) (S.mul_mem ht ht) htt _ h2
    · rw [hφc (t⁻¹ * (t * z * t⁻¹) * t) z _ hzJ₀ (by group)]
      exact h1
  have hRS : ∀ s ∈ S, ∀ z ∈ R, s * z * s⁻¹ ∈ R := by
    intro s hs z hz
    rcases hSorb s hs with hsJ | hsJ
    · exact hRs s hs hsJ z hz
    · have h1 := hRt _ (hRs (t⁻¹ * s) (S.mul_mem (S.inv_mem ht) hs) hsJ z hz)
      have h2 : t * (t⁻¹ * s * z * (t⁻¹ * s)⁻¹) * t⁻¹ = s * z * s⁻¹ := by group
      rwa [h2] at h1
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hRS s hs z, fun h => ?_⟩
    have h1 := hRS s⁻¹ (S.inv_mem hs) _ h
    have h2 : s⁻¹ * (s * z * s⁻¹) * s⁻¹⁻¹ = z := by group
    rwa [h2] at h1
  obtain ⟨b₀, rfl⟩ := piX_surjective J y
  have hb₀J₀ : (b₀ : G) ∈ J₀ := Subgroup.mem_sup_left b₀.2
  have htb₀ : t * (b₀ : G) * t⁻¹ ∈ M := htJM b₀ b₀.2
  have hb : (b₀ : G) * (t * b₀ * t⁻¹) ∈ J₀ := J₀.mul_mem hb₀J₀ (Subgroup.mem_sup_right htb₀)
  have hφb : φ ⟨(b₀ : G) * (t * b₀ * t⁻¹), hb⟩ = piX J b₀ := projSup_eq hJM hJMK htb₀ rfl
  have hφ₂b : φ ⟨t⁻¹ * ((b₀ : G) * (t * b₀ * t⁻¹)) * t, htiJ₀ _ hb⟩ = piX J b₀ := by
    have hm : (b₀ : G)⁻¹ * (t⁻¹ * b₀ * t) * b₀ ∈ M := by
      have h1 : t⁻¹ * (b₀ : G) * t ∈ M := by simpa using htiJM b₀ b₀.2
      have h2 := (Subgroup.mem_normalizer_iff.mp (hJM (J.inv_mem b₀.2)) _).mp h1
      simpa [mul_assoc] using h2
    exact projSup_eq hJM hJMK hm (by group)
  set b := (b₀ : G) * (t * b₀ * t⁻¹) with hbdef
  have hbS₁ : ∀ s ∈ S, s ∈ Subgroup.normalizer (J : Set G) → s * b * s⁻¹ * b⁻¹ ∈ R := by
    intro s hs hsJ
    have hsb : s * b * s⁻¹ ∈ J₀ := conj_mem_sup hJM hsJ (hS₁M s hs hsJ) hb
    have hmem : s * b * s⁻¹ * b⁻¹ ∈ J₀ := J₀.mul_mem hsb (J₀.inv_mem hb)
    rw [hmemR _ hmem]
    have hs' : t⁻¹ * s * t ∈ S := S.mul_mem (S.mul_mem (S.inv_mem ht) hs) ht
    have hs'J := hS₁t s hs hsJ
    have hsb' : (t⁻¹ * s * t) * (t⁻¹ * b * t) * (t⁻¹ * s * t)⁻¹ ∈ J₀ :=
      conj_mem_sup hJM hs'J (hS₁M _ hs' hs'J) (htiJ₀ b hb)
    constructor
    · rw [hφmul _ _ hsb (J₀.inv_mem hb), hφinv _ hb, hE1 s hs hsJ b hb hsb, hφb]
      exact hyρ s hs hsJ
    · rw [hφc (t⁻¹ * (s * b * s⁻¹ * b⁻¹) * t)
        ((t⁻¹ * s * t) * (t⁻¹ * b * t) * (t⁻¹ * s * t)⁻¹ * (t⁻¹ * b * t)⁻¹) _
        (J₀.mul_mem hsb' (J₀.inv_mem (htiJ₀ b hb))) (by group),
        hφmul _ _ hsb' (J₀.inv_mem (htiJ₀ b hb)), hφinv _ (htiJ₀ b hb),
        hE1 _ hs' hs'J _ (htiJ₀ b hb) hsb', hφ₂b]
      exact hyρ _ hs' hs'J
  have hbSt : t * b * t⁻¹ * b⁻¹ ∈ R := by
    have htb : t * b * t⁻¹ ∈ J₀ := htJ₀ b hb
    have hmem : t * b * t⁻¹ * b⁻¹ ∈ J₀ := J₀.mul_mem htb (J₀.inv_mem hb)
    rw [hmemR _ hmem]
    constructor
    · rw [hφmul _ _ htb (J₀.inv_mem hb), hφinv _ hb, hE2 b hb htb, hφ₂b, hφb]
      exact hyρ (t * t) (S.mul_mem ht ht) htt
    · rw [hφc (t⁻¹ * (t * b * t⁻¹ * b⁻¹) * t) (b * (t⁻¹ * b * t)⁻¹) _
        (J₀.mul_mem hb (J₀.inv_mem (htiJ₀ b hb))) (by group),
        hφmul _ _ hb (J₀.inv_mem (htiJ₀ b hb)), hφinv _ (htiJ₀ b hb), hφb, hφ₂b, mul_inv_cancel]
      exact P.one_mem
  have hbS : ∀ s ∈ S, s * b * s⁻¹ * b⁻¹ ∈ R := by
    intro s hs
    rcases hSorb s hs with hsJ | hsJ
    · exact hbS₁ s hs hsJ
    · have h1 := R.mul_mem (hRt _ (hbS₁ (t⁻¹ * s) (S.mul_mem (S.inv_mem ht) hs) hsJ)) hbSt
      have h2 : t * ((t⁻¹ * s) * b * (t⁻¹ * s)⁻¹ * b⁻¹) * t⁻¹ * (t * b * t⁻¹ * b⁻¹) =
          s * b * s⁻¹ * b⁻¹ := by group
      rwa [h2] at h1
  have hβD : ∀ z (hz : z ∈ D), rhoX J ⟨c, hc⟩ (φ ⟨z, (hD.1 hz).1⟩) = φ ⟨z, (hD.1 hz).1⟩ := by
    intro z hz
    have h1 := projSup_conj hJM hJMK hc hcM ⟨z, (hD.1 hz).1⟩
    exact h1.symm.trans (hφc _ _ _ _ (hcD z hz))
  exact not_isCoprimePrimeAut_of_lift hS2 hQ₀ hQR hRY hSR hD φ hφR hyrig hb hφb hbS hβD

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
