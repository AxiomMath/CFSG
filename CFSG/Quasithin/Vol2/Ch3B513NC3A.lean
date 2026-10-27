module

public import CFSG.Quasithin.Background.B5P4Num

public section

namespace CFSG.Quasithin.B513N

variable {W : Type} [CommGroup W]

section Product

variable {G₁ G₂ : Subgroup (MulAut W)}

theorem exists_mul_of_mem_sup (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) {x : MulAut W}
    (hx : x ∈ G₁ ⊔ G₂) : ∃ a ∈ G₁, ∃ b ∈ G₂, a * b = x := by
  let S : Subgroup (MulAut W) :=
    { carrier := {x | ∃ a ∈ G₁, ∃ b ∈ G₂, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', G₁.mul_mem ha ha', b * b', G₂.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, G₁.one_mem, 1, G₂.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, G₁.inv_mem ha, b⁻¹, G₂.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact hc _ (G₁.inv_mem ha) _ (G₂.inv_mem hb) }
  have hle : G₁ ⊔ G₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, G₂.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, G₁.one_mem, b, hb, one_mul b⟩)
  exact hle hx

@[expose] def prj (G₁ G₂ K : Subgroup (MulAut W)) (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    Subgroup (MulAut W) where
  carrier := {a | a ∈ G₁ ∧ ∃ b ∈ G₂, a * b ∈ K}
  one_mem' := ⟨G₁.one_mem, 1, G₂.one_mem, by rw [mul_one]; exact K.one_mem⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨G₁.mul_mem ha ha', b * b', G₂.mul_mem hb hb', ?_⟩
    have e : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
        _ = (a * b) * (a' * b') := by group
    rw [e]
    exact K.mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨G₁.inv_mem ha, b⁻¹, G₂.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      rw [mul_inv_rev]
      exact hc _ (G₁.inv_mem ha) _ (G₂.inv_mem hb)
    rw [e]
    exact K.inv_mem hab

theorem prj_le (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (K : Subgroup (MulAut W)) :
    prj G₁ G₂ K hc ≤ G₁ := fun _ ha => ha.1

theorem isElemAbelian2_prj (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hd : G₁ ⊓ G₂ = ⊥)
    {K : Subgroup (MulAut W)} (hK : IsElemAbelian2 K) : IsElemAbelian2 (prj G₁ G₂ K hc) := by
  constructor
  · rintro a ⟨ha, b, hb, hab⟩ a' ⟨ha', b', hb', hab'⟩
    have h1 := hK.1 _ hab _ hab'
    have e1 : a * b * (a' * b') = a * a' * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [hc a' ha' b hb]
        _ = a * a' * (b * b') := by group
    have e2 : a' * b' * (a * b) = a' * a * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [hc a ha b' hb']
        _ = a' * a * (b' * b) := by group
    rw [e1, e2] at h1
    have hmem : (a' * a)⁻¹ * (a * a') ∈ G₁ ⊓ G₂ := by
      refine ⟨G₁.mul_mem (G₁.inv_mem (G₁.mul_mem ha' ha)) (G₁.mul_mem ha ha'), ?_⟩
      have e3 : (a' * a)⁻¹ * (a * a') = (b' * b) * (b * b')⁻¹ := by
        calc (a' * a)⁻¹ * (a * a') = (a' * a)⁻¹ * (a * a' * (b * b')) * (b * b')⁻¹ := by group
          _ = (a' * a)⁻¹ * (a' * a * (b' * b)) * (b * b')⁻¹ := by rw [h1]
          _ = (b' * b) * (b * b')⁻¹ := by group
      rw [e3]
      exact G₂.mul_mem (G₂.mul_mem hb' hb) (G₂.inv_mem (G₂.mul_mem hb hb'))
    rw [hd, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  · rintro a ⟨ha, b, hb, hab⟩
    have h2 := hK.2 _ hab
    have e : (a * b) ^ 2 = a ^ 2 * b ^ 2 := (Commute.mul_pow (hc a ha b hb) 2)
    rw [e] at h2
    have hmem : a ^ 2 ∈ G₁ ⊓ G₂ := by
      refine ⟨G₁.pow_mem ha 2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h2]
      exact G₂.inv_mem (G₂.pow_mem hb 2)
    rw [hd, Subgroup.mem_bot] at hmem
    exact hmem

variable [Finite W]

theorem card_le_card_prj_mul (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    {K : Subgroup (MulAut W)} (hK : K ≤ G₁ ⊔ G₂) :
    Nat.card K ≤ Nat.card (prj G₁ G₂ K hc) * Nat.card ↥(K ⊓ G₂) := by
  classical
  have hdec : ∀ k : ↥K, ∃ a ∈ G₁, ∃ b ∈ G₂, a * b = (k : MulAut W) := fun k =>
    exists_mul_of_mem_sup hc (hK k.2)
  choose a ha b hb hab using hdec
  have hrep : ∀ p : ↥(prj G₁ G₂ K hc), ∃ c ∈ G₂, (p : MulAut W) * c ∈ K := fun p => p.2.2
  choose c hc' hcK using hrep
  let pa : ↥K → ↥(prj G₁ G₂ K hc) := fun k =>
    ⟨a k, ha k, b k, hb k, by rw [hab k]; exact k.2⟩
  have hmemK : ∀ k : ↥K, ((pa k : MulAut W) * c (pa k))⁻¹ * (k : MulAut W) ∈ K ⊓ G₂ := by
    intro k
    refine ⟨K.mul_mem (K.inv_mem (hcK (pa k))) k.2, ?_⟩
    have e : ((pa k : MulAut W) * c (pa k))⁻¹ * (k : MulAut W) = (c (pa k))⁻¹ * b k := by
      show (a k * c (pa k))⁻¹ * (k : MulAut W) = _
      rw [← hab k]
      group
    rw [e]
    exact G₂.mul_mem (G₂.inv_mem (hc' (pa k))) (hb k)
  let f : ↥K → ↥(prj G₁ G₂ K hc) × ↥(K ⊓ G₂) := fun k => (pa k, ⟨_, hmemK k⟩)
  have hf : Function.Injective f := by
    intro k k' hkk'
    have h1 : pa k = pa k' := congrArg Prod.fst hkk'
    have h2 := congrArg (fun p => ((p.2 : ↥(K ⊓ G₂)) : MulAut W)) hkk'
    simp only [f] at h2
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  calc Nat.card K ≤ Nat.card (↥(prj G₁ G₂ K hc) × ↥(K ⊓ G₂)) := Nat.card_le_card_of_injective f hf
    _ = _ := Nat.card_prod _ _

omit [Finite W] in
theorem fixV_prj_inf (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) {K : Subgroup (MulAut W)}
    (hK : K ≤ G₁ ⊔ G₂) {Y : Subgroup W} (hY : ∀ g ∈ G₂, ∀ y ∈ Y, g y = y) :
    fixV (prj G₁ G₂ K hc) ⊓ Y = fixV K ⊓ Y := by
  ext y
  constructor
  · rintro ⟨hy, hyY⟩
    refine ⟨fun k hk => ?_, hyY⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc (hK hk)
    rw [MulAut.mul_apply, hY b hb y hyY]
    exact hy a ⟨ha, b, hb, hk⟩
  · rintro ⟨hy, hyY⟩
    refine ⟨fun p hp => ?_, hyY⟩
    obtain ⟨-, b, hb, hpb⟩ := hp
    have h1 := hy _ hpb
    rw [MulAut.mul_apply, hY b hb y hyY] at h1
    exact h1

end Product

variable [Finite W]

theorem card_mul_le_of_fix {X A G₂ : Subgroup (MulAut W)} (hA : IsFFStarOffender X A)
    {Y : Subgroup W} (hY : ∀ g ∈ G₂, ∀ y ∈ Y, g y = y) :
    Nat.card Y * Nat.card ↥(A ⊓ G₂) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ Y) := by
  have hoff := hA.2.2.2 (A ⊓ G₂) inf_le_left
  have hsub : Y ⊔ fixV A ≤ fixV (A ⊓ G₂) := sup_le (fun y hy g hg => hY g hg.2 y hy)
    (fun w hw g hg => hw g hg.1)
  have h1 : (fixV A).relIndex (Y ⊔ fixV A) = (fixV A).relIndex Y :=
    Subgroup.relIndex_sup_right Y (fixV A)
  have h2 := Subgroup.relIndex_mul_card (fixV A) (Y ⊔ fixV A)
  rw [inf_eq_left.2 le_sup_right, h1] at h2
  have h3 := Subgroup.relIndex_mul_card (fixV A) Y
  have hF : 0 < Nat.card (fixV A) := Nat.card_pos
  have h4 : Nat.card ↥(A ⊓ G₂) * (fixV A).relIndex Y * Nat.card (fixV A) ≤
      Nat.card A * Nat.card (fixV A) := by
    calc Nat.card ↥(A ⊓ G₂) * (fixV A).relIndex Y * Nat.card (fixV A)
        = Nat.card ↥(A ⊓ G₂) * Nat.card ↥(Y ⊔ fixV A) := by rw [← h2]; ring
      _ ≤ Nat.card ↥(A ⊓ G₂) * Nat.card (fixV (A ⊓ G₂)) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hsub)
      _ ≤ Nat.card A * Nat.card (fixV A) := hoff
  have h5 : Nat.card ↥(A ⊓ G₂) * (fixV A).relIndex Y ≤ Nat.card A :=
    Nat.le_of_mul_le_mul_right h4 hF
  calc Nat.card Y * Nat.card ↥(A ⊓ G₂)
      = Nat.card ↥(A ⊓ G₂) * (fixV A).relIndex Y * Nat.card ↥(fixV A ⊓ Y) := by rw [← h3]; ring
    _ ≤ Nat.card A * Nat.card ↥(fixV A ⊓ Y) := Nat.mul_le_mul_right _ h5

theorem exists_isFFStarMin_le_left {G G₁ G₂ : Subgroup (MulAut W)} (hJ : G = ffJ G)
    (hsup : G₁ ⊔ G₂ = G) (hd : G₁ ⊓ G₂ = ⊥) (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hne : G₁ ≠ ⊥) {W₁ W₂ : Subgroup W} (hW12 : W₁ ⊔ W₂ = ⊤)
    (h1 : ∀ g ∈ G₁, ∀ w ∈ W₂, g w = w) (h2 : ∀ g ∈ G₂, ∀ w ∈ W₁, g w = w) :
    ∃ D, IsFFStarMin G D ∧ D ≤ G₁ := by
  obtain ⟨A, hA, hAG₂⟩ : ∃ A, IsFFStarOffender G A ∧ ¬ A ≤ G₂ := by
    by_contra hno
    push Not at hno
    apply hne
    have hGG₂ : G ≤ G₂ := by
      rw [hJ]
      exact iSup₂_le fun A hA => hno A hA
    rw [eq_bot_iff]
    intro g hg
    have hg' : g ∈ G₁ ⊓ G₂ := ⟨hg, hGG₂ (hsup ▸ Subgroup.mem_sup_left hg)⟩
    rw [hd] at hg'
    exact hg'
  have hAG : A ≤ G₁ ⊔ G₂ := hsup ▸ hA.1
  set B := prj G₁ G₂ A hc with hB
  have hBne : B ≠ ⊥ := by
    intro hbot
    apply hAG₂
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc (hAG hx)
    have haB : a ∈ B := ⟨ha, b, hb, hx⟩
    rw [hbot, Subgroup.mem_bot] at haB
    rw [haB, one_mul]
    exact hb
  have ht := card_mul_le_of_fix hA h2 (Y := W₁)
  have hcard := card_le_card_prj_mul hc hAG
  have hfix := fixV_prj_inf hc hAG h2 (Y := W₁)
  have hpos : 0 < Nat.card ↥(A ⊓ G₂) := Nat.card_pos
  have hW₁ : Nat.card W₁ ≤ Nat.card B * Nat.card ↥(fixV B ⊓ W₁) := by
    rw [hfix]
    have : Nat.card W₁ * Nat.card ↥(A ⊓ G₂) ≤
        Nat.card B * Nat.card ↥(fixV A ⊓ W₁) * Nat.card ↥(A ⊓ G₂) := by
      calc Nat.card W₁ * Nat.card ↥(A ⊓ G₂) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ W₁) := ht
        _ ≤ Nat.card B * Nat.card ↥(A ⊓ G₂) * Nat.card ↥(fixV A ⊓ W₁) :=
            Nat.mul_le_mul_right _ hcard
        _ = Nat.card B * Nat.card ↥(fixV A ⊓ W₁) * Nat.card ↥(A ⊓ G₂) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hW2B : W₂ ≤ fixV B := fun w hw g hg => h1 g (prj_le hc A hg) w hw
  have hrel : (fixV B).relIndex W₁ = (fixV B).index := by
    rw [← Subgroup.relIndex_sup_right W₁ (fixV B)]
    have htop : W₁ ⊔ fixV B = ⊤ := eq_top_iff.2 (hW12 ▸ sup_le_sup_left hW2B W₁)
    rw [htop, Subgroup.relIndex_top_right]
  have hWcard : Nat.card W ≤ Nat.card B * Nat.card (fixV B) := by
    have e1 := Subgroup.relIndex_mul_card (fixV B) W₁
    have e2 := Subgroup.index_mul_card (fixV B)
    rw [hrel] at e1
    have hpos' : 0 < Nat.card ↥(fixV B ⊓ W₁) := Nat.card_pos
    have h3 : (fixV B).index ≤ Nat.card B := by
      have : (fixV B).index * Nat.card ↥(fixV B ⊓ W₁) ≤
          Nat.card B * Nat.card ↥(fixV B ⊓ W₁) := by rw [e1]; exact hW₁
      exact Nat.le_of_mul_le_mul_right this hpos'
    rw [← e2]
    exact Nat.mul_le_mul_right _ h3
  have hA2 : IsA2 G B :=
    ⟨(prj_le hc A).trans (hsup ▸ le_sup_left), hBne, isElemAbelian2_prj hc hd hA.2.2.1⟩
  obtain ⟨B', hB'B, hB', -⟩ := B1.exists_offender_below hA2 0 (by simpa using hWcard)
  obtain ⟨D, hD, hDB'⟩ := B5.exists_isFFStarMin_ffLe hB'
  exact ⟨D, hD, hDB'.2.2.1.trans (hB'B.trans (prj_le hc A))⟩

section Centralize

variable {G Gi Gj : Subgroup (MulAut W)} {Wi Wj : Subgroup W}

omit [Finite W] in
theorem mul_inv_mem_fixV (hGi : Gi ≤ G) (hWi : commV Gi ≤ Wi)
    (hinvj : ∀ g ∈ G, ∀ w ∈ Wj, g w ∈ Wj) (hinf : Wi ⊓ Wj = fixV G) {g : MulAut W}
    (hg : g ∈ Gi) {w : W} (hw : w ∈ Wj) : g w * w⁻¹ ∈ fixV G := by
  rw [← hinf]
  exact ⟨hWi (Subgroup.subset_closure ⟨g, hg, w, rfl⟩),
    Wj.mul_mem (hinvj g (hGi hg) w hw) (Wj.inv_mem hw)⟩

omit [Finite W] in
theorem fix_of_perfect (hGi : Gi ≤ G) (hperf : ⁅Gi, Gi⁆ = Gi) (hWi : commV Gi ≤ Wi)
    (hinvj : ∀ g ∈ G, ∀ w ∈ Wj, g w ∈ Wj) (hinf : Wi ⊓ Wj = fixV G) :
    ∀ g ∈ Gi, ∀ w ∈ Wj, g w = w := by
  intro g hg w hw
  let S : Subgroup (MulAut W) :=
    { carrier := {x | x w = w}
      mul_mem' := fun {x y} hx hy => by
        show (x * y) w = w
        rw [MulAut.mul_apply, hy, hx]
      one_mem' := rfl
      inv_mem' := fun {x} hx => by
        show x⁻¹ w = w
        conv_lhs => rw [← hx]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] }
  have hc : ∀ x ∈ Gi, x w = (x w * w⁻¹) * w := fun x _ => by rw [inv_mul_cancel_right]
  have hcfix : ∀ x ∈ Gi, ∀ y ∈ G, y (x w * w⁻¹) = x w * w⁻¹ := fun x hx y hy =>
    mul_inv_mem_fixV hGi hWi hinvj hinf hx hw y hy
  have hinvw : ∀ x ∈ Gi, x⁻¹ w = (x w * w⁻¹)⁻¹ * w := by
    intro x hx
    have h1 : x⁻¹ (x w) = w := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [hc x hx, map_mul, hcfix x hx x⁻¹ (G.inv_mem (hGi hx))] at h1
    rw [eq_inv_mul_iff_mul_eq]
    exact h1
  have hfixc : ∀ z ∈ G, ∀ x ∈ Gi, ∀ v : W, z ((x w * w⁻¹)⁻¹ * v) = (x w * w⁻¹)⁻¹ * z v := by
    intro z hz x hx v
    rw [map_mul, map_inv, hcfix x hx z hz]
  have hfixc' : ∀ z ∈ G, ∀ x ∈ Gi, ∀ v : W, z ((x w * w⁻¹) * v) = (x w * w⁻¹) * z v := by
    intro z hz x hx v
    rw [map_mul, hcfix x hx z hz]
  have hle : ⁅Gi, Gi⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    show (x * y * x⁻¹ * y⁻¹) w = w
    have hx' : x ∈ G := hGi hx
    have hy' : y ∈ G := hGi hy
    calc (x * y * x⁻¹ * y⁻¹) w = x (y (x⁻¹ (y⁻¹ w))) := rfl
      _ = x (y (x⁻¹ ((y w * w⁻¹)⁻¹ * w))) := by rw [hinvw y hy]
      _ = x (y ((y w * w⁻¹)⁻¹ * ((x w * w⁻¹)⁻¹ * w))) := by
          rw [hfixc x⁻¹ (G.inv_mem hx') y hy, hinvw x hx]
      _ = x ((y w * w⁻¹)⁻¹ * ((x w * w⁻¹)⁻¹ * ((y w * w⁻¹) * w))) := by
          rw [hfixc y hy' y hy, hfixc y hy' x hx, ← hc y hy]
      _ = (y w * w⁻¹)⁻¹ * ((x w * w⁻¹)⁻¹ * ((y w * w⁻¹) * ((x w * w⁻¹) * w))) := by
          rw [hfixc x hx' y hy, hfixc x hx' x hx, hfixc' x hx' y hy, ← hc x hx]
      _ = w := by
          rw [mul_left_comm (x w * w⁻¹)⁻¹, ← mul_assoc, inv_mul_cancel, one_mul,
            ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hperf] at hle
  exact hle hg

omit [Finite W] in
theorem fix_commV_sup (hGi : Gi ≤ G) (hGj : Gj ≤ G) (hcomm : ∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a)
    (hWi : commV Gi ≤ Wi) (hWjc : commV Gj ≤ Wj) (hinvi : ∀ g ∈ G, ∀ w ∈ Wi, g w ∈ Wi)
    (hinvj : ∀ g ∈ G, ∀ w ∈ Wj, g w ∈ Wj) (hinf : Wi ⊓ Wj = fixV G) (hsupW : Wi ⊔ Wj = ⊤) :
    ∀ g ∈ Gi, ∀ w ∈ commV Gj ⊔ fixV G, g w = w := by
  intro g hg
  let S : Subgroup W :=
    { carrier := {u | g u = u}
      mul_mem' := fun {x y} hx hy => by
        show g (x * y) = x * y
        rw [map_mul, hx, hy]
      one_mem' := map_one g
      inv_mem' := fun {x} hx => by
        show g x⁻¹ = x⁻¹
        rw [map_inv, hx] }
  have hCS : fixV G ≤ S := fun c hc => hc g (hGi hg)
  have hstep : ∀ h ∈ Gj, ∀ w ∈ Wj, g (h w * w⁻¹) = h w * w⁻¹ := by
    intro h hh w hw
    have hx := mul_inv_mem_fixV hGi hWi hinvj hinf hg hw
    have hgw : g w = (g w * w⁻¹) * w := by rw [inv_mul_cancel_right]
    have hgh : g (h w) = h (g w) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm g hg h hh]
    rw [map_mul, map_inv, hgh, hgw, map_mul, hx h (hGj hh)]
    rw [← hgw]
    calc g w * w⁻¹ * h w * (g w)⁻¹ = h w * w⁻¹ * (g w * (g w)⁻¹) := by ac_rfl
      _ = h w * w⁻¹ := by rw [mul_inv_cancel, mul_one]
  have hstep' : ∀ h ∈ Gj, ∀ v ∈ Wi, h v * v⁻¹ ∈ fixV G := by
    intro h hh v hv
    rw [← hinf]
    exact ⟨Wi.mul_mem (hinvi h (hGj hh) v hv) (Wi.inv_mem hv),
      hWjc (Subgroup.subset_closure ⟨h, hh, v, rfl⟩)⟩
  have hcomm' : commV Gj ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨h, hh, v, rfl⟩
    have hv : v ∈ Wi ⊔ Wj := by rw [hsupW]; trivial
    obtain ⟨vi, hvi, vj, hvj, rfl⟩ := Subgroup.mem_sup.1 hv
    have e : h (vi * vj) * (vi * vj)⁻¹ = (h vi * vi⁻¹) * (h vj * vj⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    show g (h (vi * vj) * (vi * vj)⁻¹) = h (vi * vj) * (vi * vj)⁻¹
    rw [e, map_mul, hstep h hh vj hvj, hstep' h hh vi hvi g (hGi hg)]
  intro w hw
  exact (sup_le hcomm' hCS) hw

omit [Finite W] in
theorem fix_of_eq_sup (hGi : Gi ≤ G) (hGj : Gj ≤ G) (hcomm : ∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a)
    (hWi : commV Gi ≤ Wi) (hinvi : ∀ g ∈ G, ∀ w ∈ Wi, g w ∈ Wi)
    (hinvj : ∀ g ∈ G, ∀ w ∈ Wj, g w ∈ Wj) (hinf : Wi ⊓ Wj = fixV G) (hsupW : Wi ⊔ Wj = ⊤)
    (hWj : Wj = commV Gj ⊔ fixV G) : ∀ g ∈ Gi, ∀ w ∈ Wj, g w = w := by
  intro g hg w hw
  have hWjc : commV Gj ≤ Wj := by rw [hWj]; exact le_sup_left
  rw [hWj] at hw
  exact fix_commV_sup hGi hGj hcomm hWi hWjc hinvi hinvj hinf hsupW g hg w hw

end Centralize

end CFSG.Quasithin.B513N
