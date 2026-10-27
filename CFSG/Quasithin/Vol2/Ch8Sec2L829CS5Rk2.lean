module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Rk1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Rk2

variable {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ}

theorem isPGroup_of_sq_eq_one_cs5 {E : Subgroup Y} (h : ∀ x ∈ E, x ^ 2 = 1) : IsPGroup 2 E := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa using h x x.2

theorem le_of_isPGroup_of_sylow_le_cs5 [Finite Y] {X S M : Subgroup Y} (hS : IsSylowTwoOf S X)
    (hM : IsPGroup 2 M) (hSM : S ≤ M) (hMX : M ≤ X) : M ≤ S := by
  have h1 : S.relIndex M * M.relIndex X = S.relIndex X :=
    Subgroup.relIndex_mul_relIndex S M X hSM hMX
  have hodd : ¬ 2 ∣ S.relIndex X := hS.2.2
  have h2 : ¬ 2 ∣ S.relIndex M := fun h => hodd (h1 ▸ h.mul_right _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM' : IsPGroup 2 ↥M := hM
  obtain ⟨k, hk⟩ := hM'.index (S.subgroupOf M)
  have hk0 : k = 0 := by
    by_contra hk0
    exact h2 (by rw [Subgroup.relIndex, hk]; exact dvd_pow_self 2 hk0)
  rw [hk0, pow_zero] at hk
  have : S.relIndex M = 1 := hk
  exact (Subgroup.relIndex_eq_one.mp this)

theorem isSylowTwoOf_conjSub_cs5 [Finite Y] {X S : Subgroup Y} [X.Normal] (hS : IsSylowTwoOf S X)
    (y : Y) : IsSylowTwoOf (B6.conjSub y S) X := by
  have hX : X.map (MulAut.conj y).toMonoidHom = X := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance z hz y
    · intro hx
      refine ⟨y⁻¹ * x * y, ?_, by simp [mul_assoc]⟩
      have := Subgroup.Normal.conj_mem (inferInstance : X.Normal) x hx y⁻¹
      simpa using this
  have hconj : B6.conjSub y S = S.map (MulAut.conj y).toMonoidHom := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hconj, ← hX]
    exact Subgroup.map_mono hS.1
  · rw [hconj]
    exact hS.2.1.map _
  · have h := Subgroup.relIndex_map_map_of_injective S X (f := (MulAut.conj y).toMonoidHom)
      (MulAut.conj y).injective
    rw [hX] at h
    have h2 : ((B6.conjSub y S).subgroupOf X).index = (S.subgroupOf X).index := by
      rw [hconj]
      exact h
    rw [h2]
    exact hS.2.2

theorem exists_conj_le_of_isPGroup_cs5 [Finite Y] {X S P : Subgroup Y} (hS : IsSylowTwoOf S X)
    (hPX : P ≤ X) (hP : IsPGroup 2 P) : ∃ g ∈ X, P ≤ B6.conjSub g S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SS : Sylow 2 ↥X := (hS.2.1.comap_subtype (K := X)).toSylow hS.2.2
  have hP' : IsPGroup 2 (P.subgroupOf X) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X SS Q
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 : (⟨y, hPX hy⟩ : ↥X) ∈ Q := hQ (by simpa [Subgroup.mem_subgroupOf] using hy)
  rw [← hx] at h1
  have h2 : (⟨y, hPX hy⟩ : ↥X) ∈ ((x • SS : Sylow 2 ↥X) : Subgroup ↥X) := h1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : (MulAut.conj x)⁻¹ • (⟨y, hPX hy⟩ : ↥X) ∈ (SS : Subgroup ↥X) := h2
  have h4 : (MulAut.conj x)⁻¹ • (⟨y, hPX hy⟩ : ↥X) ∈ S.subgroupOf X := h3
  rw [B6.mem_conjSub]
  simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply, mul_assoc] using h4

theorem exists_conj_eq_of_isSylowTwoOf_cs5 [Finite Y] [X.Normal] {S P : Subgroup Y}
    (hS : IsSylowTwoOf S X) (hP : IsSylowTwoOf P X) : ∃ g ∈ X, P = B6.conjSub g S := by
  obtain ⟨g, hg, hle⟩ := exists_conj_le_of_isPGroup_cs5 hS hP.1 hP.2.1
  refine ⟨g, hg, le_antisymm hle ?_⟩
  have hSg := isSylowTwoOf_conjSub_cs5 hS g
  exact le_of_isPGroup_of_sylow_le_cs5 hP hSg.2.1 hle hSg.1

theorem RankOneSyl.le_of_centerSub_le [Finite Y] [X.Normal] (hR : RankOneSyl X S q)
    {P : Subgroup Y} (hPX : P ≤ X) (hP : IsPGroup 2 P) (hZP : centerSub S ≤ P) : P ≤ S := by
  obtain ⟨g, hg, hle⟩ := exists_conj_le_of_isPGroup_cs5 hR.sylow hPX hP
  by_cases hgN : g ∈ Subgroup.normalizer (S : Set Y)
  · rw [B6.conjSub_eq_self hgN] at hle
    exact hle
  · exfalso
    have hZ : centerSub S ≤ S ⊓ B6.conjSub g S := le_inf (centerSub_le_cs5 S) (hZP.trans hle)
    rw [hR.ti g hg hgN] at hZ
    exact centerSub_ne_bot_cs5 hR (le_bot_iff.mp hZ)

theorem conjSub_le_of_normal_cs5 {X P : Subgroup Y} [X.Normal] (hPX : P ≤ X) (y : Y) :
    B6.conjSub y P ≤ X := by
  intro z hz
  rw [B6.mem_conjSub] at hz
  have := Subgroup.Normal.conj_mem inferInstance _ (hPX hz) y
  simpa [mul_assoc] using this

theorem le_normalizer_inf_cs5 {W N Z : Subgroup Y} (hZW : Z ≤ W)
    (hN : ∀ w ∈ W, ∀ n ∈ N, w * n * w⁻¹ ∈ N) :
    Z ≤ Subgroup.normalizer ((W ⊓ N : Subgroup Y) : Set Y) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rintro ⟨hdW, hdN⟩
    exact ⟨W.mul_mem (W.mul_mem (hZW hz) hdW) (W.inv_mem (hZW hz)), hN z (hZW hz) d hdN⟩
  · rintro ⟨h1, h2⟩
    have hz' : z⁻¹ ∈ W := W.inv_mem (hZW hz)
    refine ⟨?_, ?_⟩
    · have := W.mul_mem (W.mul_mem hz' h1) (hZW hz)
      simpa [mul_assoc] using this
    · have := hN z⁻¹ hz' _ h2
      simpa [mul_assoc] using this

theorem rk1_main [Finite Y] [X.Normal] {E : Subgroup Y} {h : Y} {N : Subgroup Y} {m : ℕ}
    (hR : RankOneSyl X S q)
    (hC : ∀ y : Y, (∀ x ∈ X, y * x = x * y) → y = 1)
    (hYX : IsPGroup 2 (Y ⧸ X))
    (hBsol : Group.IsSolvable ↥(X ⊓ Subgroup.normalizer (S : Set Y)))
    (hE : IsElemAbelian 2 E)
    (hEB : X ⊓ Subgroup.normalizer (S : Set Y) ≤ Subgroup.normalizer (E : Set Y))
    (hNnorm : ∀ i ∈ E ⊔ B6.conjSub h E, ∀ n ∈ N, i * n * i⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N)
    (hm : Nat.card (↥(E ⊔ B6.conjSub h E) ⧸ N.subgroupOf (E ⊔ B6.conjSub h E)) ≤ m)
    (hns : ¬ Group.IsSolvable ↥(E ⊔ B6.conjSub h E)) :
    centerSub S ≤ E ∧ B6.conjSub h S ≠ S ∧
      centerSub S ⊔ B6.conjSub h (centerSub S) ≤ X ∧
      q * q ≤ Nat.card ↥(centerSub S ⊔ B6.conjSub h (centerSub S)) ∧
      Nat.card ↥(centerSub S ⊔ B6.conjSub h (centerSub S)) ≤ m := by
  have hSX : S ≤ X := hR.le
  have hSB : S ≤ X ⊓ Subgroup.normalizer (S : Set Y) := le_inf hSX Subgroup.le_normalizer
  have hZne : centerSub S ≠ ⊥ := centerSub_ne_bot_cs5 hR
  have hZS : centerSub S ≤ S := centerSub_le_cs5 S
  have hEX : E ⊓ X ≠ ⊥ := by
    intro hbot
    apply hns
    have hE1 : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro e he
      refine hR.rigidity hC fun b hb => ?_
      have h1 : e * b * e⁻¹ * b⁻¹ ∈ E ⊓ X := by
        refine ⟨?_, X.mul_mem (Subgroup.Normal.conj_mem inferInstance b hb.1 e) (X.inv_mem hb.1)⟩
        have : b * e⁻¹ * b⁻¹ ∈ E :=
          (Subgroup.mem_normalizer_iff.mp (hEB hb) e⁻¹).mp (E.inv_mem he)
        have h2 := E.mul_mem he this
        simpa [mul_assoc] using h2
      rw [hbot] at h1
      have h2 : e * b * e⁻¹ * b⁻¹ = 1 := h1
      calc e * b = (e * b * e⁻¹ * b⁻¹) * (b * e) := by group
        _ = b * e := by rw [h2]; simp
    have hbot : B6.conjSub h (⊥ : Subgroup Y) = ⊥ := by
      ext x
      simp [B6.mem_conjSub]
    have : E ⊔ B6.conjSub h E = ⊥ := by rw [hE1, hbot]; simp
    rw [this]
    infer_instance
  have hD₀2 : IsPGroup 2 (E ⊓ X : Subgroup Y) :=
    isPGroup_of_sq_eq_one_cs5 fun x hx => hE.2 x hx.1
  have hSnormD₀ : S ≤ Subgroup.normalizer ((E ⊓ X : Subgroup Y) : Set Y) := by
    intro s hs
    have hsB := hSB hs
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · rintro ⟨hdE, hdX⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hEB hsB) d).mp hdE,
        X.mul_mem (X.mul_mem hsB.1 hdX) (X.inv_mem hsB.1)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hEB hsB) d).mpr h1, ?_⟩
      have := X.mul_mem (X.mul_mem (X.inv_mem hsB.1) h2) hsB.1
      simpa [mul_assoc] using this
  have hD₀S : E ⊓ X ≤ S := by
    have hP2 : IsPGroup 2 (S ⊔ (E ⊓ X) : Subgroup Y) :=
      IsPGroup.to_sup_of_normal_right' hR.isPGroup hD₀2 hSnormD₀
    exact le_sup_right.trans
      (le_of_isPGroup_of_sylow_le_cs5 hR.sylow hP2 le_sup_left (sup_le hSX inf_le_right))
  have hZE : centerSub S ≤ E := by
    haveI : Group.IsNilpotent ↥S := hR.isPGroup.isNilpotent
    have hnorm : ((E ⊓ X).subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hD₀S).mpr hSnormD₀
    have hD₁ne : (E ⊓ X).subgroupOf S ≠ ⊥ := by
      intro hb
      apply hEX
      rw [Subgroup.eq_bot_iff_forall] at hb ⊢
      intro x hx
      have := hb ⟨x, hD₀S hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa using congrArg Subtype.val this
    have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hD₁ne
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h1
    obtain ⟨hcD, hcZ⟩ := c.2
    have hz₁E : ((c : ↥S) : Y) ∈ E ⊓ X := by simpa [Subgroup.mem_subgroupOf] using hcD
    have hz₁Z : ((c : ↥S) : Y) ∈ centerSub S := by
      rw [mem_centerSub_cs5]
      refine ⟨(c : ↥S).2, fun s hs => ?_⟩
      have := Subgroup.mem_center_iff.mp hcZ ⟨s, hs⟩
      exact congrArg Subtype.val this
    have hz₁ne : ((c : ↥S) : Y) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext (by simpa using h')))
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact E.one_mem
    · obtain ⟨b, hb, hbz⟩ := hR.ztrans _ hz₁Z hz₁ne z hz hz1
      rw [← hbz]
      exact (Subgroup.mem_normalizer_iff.mp (hEB hb) _).mp hz₁E.1
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (S : Set Y) := by
    intro e he
    have hSe := isSylowTwoOf_conjSub_cs5 hR.sylow e
    obtain ⟨g, hg, hgeq⟩ := exists_conj_eq_of_isSylowTwoOf_cs5 hR.sylow hSe
    by_cases hgN : g ∈ Subgroup.normalizer (S : Set Y)
    · rw [B6.conjSub_eq_self hgN] at hgeq
      refine B6.mem_normalizer_of_conjSub_le hgeq.le ?_
      have : B6.conjSub e⁻¹ S = S := by
        calc B6.conjSub e⁻¹ S = B6.conjSub e⁻¹ (B6.conjSub e S) := by rw [hgeq]
          _ = B6.conjSub (e⁻¹ * e) S := by rw [B6.conjSub_mul]
          _ = S := by simp [B6.conjSub_one]
      exact this.le
    · exfalso
      have hZ1 : centerSub S ≤ B6.conjSub e S := by
        intro z hz
        rw [B6.mem_conjSub]
        have hzE := hZE hz
        have hcomm := hE.1.is_comm.comm ⟨e⁻¹, E.inv_mem he⟩ ⟨z, hzE⟩
        have hcomm' : e⁻¹ * z = z * e⁻¹ := congrArg Subtype.val hcomm
        have : e⁻¹ * z * e = z := by rw [hcomm']; group
        rw [this]
        exact hZS hz
      rw [hgeq] at hZ1
      have hZ2 : centerSub S ≤ S ⊓ B6.conjSub g S := le_inf hZS hZ1
      rw [hR.ti g hg hgN] at hZ2
      exact hZne (le_bot_iff.mp hZ2)
  have hne : B6.conjSub h S ≠ S := by
    intro heq
    apply hns
    have hsol := isSolvable_normalizer_of_borel_cs5 hSX hYX hBsol
    have hle : E ⊔ B6.conjSub h E ≤ Subgroup.normalizer (S : Set Y) := by
      refine sup_le hEN ?_
      intro x hx
      rw [B6.mem_conjSub] at hx
      have h1 : x ∈ Subgroup.normalizer ((B6.conjSub h S : Subgroup Y) : Set Y) :=
        mem_normalizer_conjSub_cs5.mpr (hEN _ hx)
      rwa [heq] at h1
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hSS' : S ⊓ B6.conjSub h S = ⊥ := by
    have hsyl := isSylowTwoOf_conjSub_cs5 hR.sylow h
    obtain ⟨g, hg, hgeq⟩ := exists_conj_eq_of_isSylowTwoOf_cs5 hR.sylow hsyl
    have hgN : g ∉ Subgroup.normalizer (S : Set Y) := by
      intro hgN
      apply hne
      rw [hgeq]
      exact B6.conjSub_eq_self hgN
    rw [hgeq]
    exact hR.ti g hg hgN
  set W : Subgroup Y := centerSub S ⊔ B6.conjSub h (centerSub S) with hW
  have hZ'S' : B6.conjSub h (centerSub S) ≤ B6.conjSub h S := (B6.conjSub h).monotone hZS
  have hZ'E' : B6.conjSub h (centerSub S) ≤ B6.conjSub h E := (B6.conjSub h).monotone hZE
  have hZ'X : B6.conjSub h (centerSub S) ≤ X :=
    conjSub_le_of_normal_cs5 (hZS.trans hSX) h
  have hWX : W ≤ X := sup_le (hZS.trans hSX) hZ'X
  have hWI : W ≤ E ⊔ B6.conjSub h E :=
    sup_le (hZE.trans le_sup_left) (hZ'E'.trans le_sup_right)
  have hZZ' : centerSub S ⊓ B6.conjSub h (centerSub S) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc centerSub S ⊓ B6.conjSub h (centerSub S) ≤ S ⊓ B6.conjSub h S :=
          inf_le_inf hZS hZ'S'
      _ = ⊥ := hSS'
  have hcardZ' : Nat.card ↥(B6.conjSub h (centerSub S)) = q := by
    rw [← hR.zcard]
    exact Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hqq : q * q ≤ Nat.card ↥W := by
    have := card_mul_le_card_sup_cs5 hZZ'
    rw [hcardZ', hR.zcard] at this
    exact this
  have hD'2 : IsPGroup 2 (W ⊓ N : Subgroup Y) := hN2.to_le inf_le_right
  have hZnorm : centerSub S ≤ Subgroup.normalizer ((W ⊓ N : Subgroup Y) : Set Y) :=
    le_normalizer_inf_cs5 le_sup_left fun w hw n hn => hNnorm w (hWI hw) n hn
  have hZ'norm : B6.conjSub h (centerSub S) ≤ Subgroup.normalizer ((W ⊓ N : Subgroup Y) : Set Y) :=
    le_normalizer_inf_cs5 le_sup_right fun w hw n hn => hNnorm w (hWI hw) n hn
  have hZ2 : IsPGroup 2 (centerSub S) := hR.isPGroup.to_le hZS
  have hZ'2 : IsPGroup 2 (B6.conjSub h (centerSub S)) := hZ2.map _
  have hDS : W ⊓ N ≤ S := by
    have hP2 : IsPGroup 2 ((W ⊓ N) ⊔ centerSub S : Subgroup Y) :=
      IsPGroup.to_sup_of_normal_left' hD'2 hZ2 hZnorm
    exact le_sup_left.trans (hR.le_of_centerSub_le (sup_le (inf_le_left.trans hWX) (hZS.trans hSX))
      hP2 le_sup_right)
  have hDS' : W ⊓ N ≤ B6.conjSub h S := by
    have hP2 : IsPGroup 2 ((W ⊓ N) ⊔ B6.conjSub h (centerSub S) : Subgroup Y) :=
      IsPGroup.to_sup_of_normal_left' hD'2 hZ'2 hZ'norm
    have hP'X : (W ⊓ N) ⊔ B6.conjSub h (centerSub S) ≤ X := sup_le (inf_le_left.trans hWX) hZ'X
    have h1 : B6.conjSub h⁻¹ ((W ⊓ N) ⊔ B6.conjSub h (centerSub S)) ≤ S := by
      refine hR.le_of_centerSub_le (conjSub_le_of_normal_cs5 hP'X h⁻¹) (hP2.map _) ?_
      intro z hz
      rw [B6.mem_conjSub]
      have hmem : h * z * h⁻¹ ∈ B6.conjSub h (centerSub S) := by
        rw [B6.mem_conjSub]
        have e : h⁻¹ * (h * z * h⁻¹) * h = z := by group
        rw [e]
        exact hz
      have := (le_sup_right : B6.conjSub h (centerSub S) ≤
        (W ⊓ N) ⊔ B6.conjSub h (centerSub S)) hmem
      simpa using this
    intro x hx
    have hx' : x ∈ (W ⊓ N) ⊔ B6.conjSub h (centerSub S) := Subgroup.mem_sup_left hx
    have h2 : h⁻¹ * x * h ∈ B6.conjSub h⁻¹ ((W ⊓ N) ⊔ B6.conjSub h (centerSub S)) := by
      rw [B6.mem_conjSub]
      simpa [mul_assoc] using hx'
    rw [B6.mem_conjSub]
    exact h1 h2
  have hD' : W ⊓ N = ⊥ := by
    refine le_bot_iff.mp ?_
    calc W ⊓ N ≤ S ⊓ B6.conjSub h S := le_inf hDS hDS'
      _ = ⊥ := hSS'
  have hinj : Function.Injective (fun w : ↥W =>
      (QuotientGroup.mk (⟨(w : Y), hWI w.2⟩ : ↥(E ⊔ B6.conjSub h E)) :
        ↥(E ⊔ B6.conjSub h E) ⧸ N.subgroupOf (E ⊔ B6.conjSub h E))) := by
    intro w₁ w₂ hw
    have h1 := QuotientGroup.eq.mp hw
    have h2 : (w₁ : Y)⁻¹ * w₂ ∈ N := by simpa [Subgroup.mem_subgroupOf] using h1
    have h3 : (w₁ : Y)⁻¹ * w₂ ∈ W ⊓ N := ⟨W.mul_mem (W.inv_mem w₁.2) w₂.2, h2⟩
    rw [hD'] at h3
    have h4 : (w₁ : Y)⁻¹ * w₂ = 1 := h3
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hcardW : Nat.card ↥W ≤ m := (Nat.card_le_card_of_injective _ hinj).trans hm
  exact ⟨hZE, hne, hWX, hqq, hcardW⟩


theorem rk1_main_of_eq [Finite Y] [X.Normal] {E I' : Subgroup Y} {h : Y} {N : Subgroup Y} {m : ℕ}
    (hR : RankOneSyl X S q)
    (hC : ∀ y : Y, (∀ x ∈ X, y * x = x * y) → y = 1)
    (hYX : IsPGroup 2 (Y ⧸ X))
    (hBsol : Group.IsSolvable ↥(X ⊓ Subgroup.normalizer (S : Set Y)))
    (hE : IsElemAbelian 2 E)
    (hEB : X ⊓ Subgroup.normalizer (S : Set Y) ≤ Subgroup.normalizer (E : Set Y))
    (hI' : I' = E ⊔ B6.conjSub h E)
    (hNnorm : ∀ i ∈ I', ∀ n ∈ N, i * n * i⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N)
    (hm : Nat.card (↥I' ⧸ N.subgroupOf I') ≤ m)
    (hns : ¬ Group.IsSolvable ↥I') :
    centerSub S ≤ E ∧ B6.conjSub h S ≠ S ∧
      centerSub S ⊔ B6.conjSub h (centerSub S) ≤ X ∧
      q * q ≤ Nat.card ↥(centerSub S ⊔ B6.conjSub h (centerSub S)) ∧
      Nat.card ↥(centerSub S ⊔ B6.conjSub h (centerSub S)) ≤ m := by
  subst hI'
  exact rk1_main hR hC hYX hBsol hE hEB hNnorm hN2 hm hns

end Rk2

end CFSG.Quasithin.H13
