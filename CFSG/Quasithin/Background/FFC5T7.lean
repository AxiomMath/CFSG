module

public import CFSG.Quasithin.Background.FFC5T5

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix CFSG.Quasithin.JonesParshall

section Count

@[expose] def commHom {V : Type} [CommGroup V] (W : Subgroup V) (a : MulAut V) (hW : ∀ w ∈ W, a w ∈ W) :
    ↥W →* ↥W where
  toFun w := ⟨a w * (w : V)⁻¹, W.mul_mem (hW w w.2) (W.inv_mem w.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    show a ((x : V) * y) * ((x : V) * y)⁻¹ = (a x * (x : V)⁻¹) * (a y * (y : V)⁻¹)
    rw [map_mul, mul_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]

theorem exists_move : ∀ γ : SL3F2, γ ≠ 1 → ∃ n : Fin 3 → ZMod 2, muF2 3 γ n ≠ n := by
  decide +kernel

theorem commHom_apply {V : Type} [CommGroup V] (W : Subgroup V) (a : MulAut V) (hW : ∀ w ∈ W, a w ∈ W)
    (w : ↥W) : ((commHom W a hW w : ↥W) : V) = a w * (w : V)⁻¹ := rfl

theorem card_commHom_le_two {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {W C : Subgroup V} {a : MulAut V} (hW : ∀ w ∈ W, a w ∈ W) (ha2 : ∀ v, a (a v) = v)
    (hCW : C ≤ W)
    (θ : ↥W →* Multiplicative (Fin 3 → ZMod 2)) (hθs : Function.Surjective θ)
    (hθk : ∀ w : ↥W, θ w = 1 ↔ (w : V) ∈ C) (hCfix : ∀ c ∈ C, a c = c)
    (hcard : Nat.card ↥W = 8 * Nat.card ↥C) {γ : SL3F2} (hγ1 : γ ≠ 1)
    (hγ : ∀ w : ↥W, θ ⟨a w, hW w w.2⟩ =
      Multiplicative.ofAdd (muF2 3 γ (Multiplicative.toAdd (θ w))))
    {x : ↥W} (hx : a x = x)
    (hxθ : ∀ n : Fin 3 → ZMod 2, Multiplicative.toAdd (θ x) ≠ muF2 3 γ n - n) :
    Nat.card (commHom W a hW).range ≤ 2 := by
  set f := commHom W a hW with hf
  have hSKr : f.range ≤ f.ker := by
    rintro _ ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [commHom_apply, commHom_apply]
    have h1 : a (a (w : V) * (w : V)⁻¹) = (w : V) * (a (w : V))⁻¹ := by
      rw [map_mul, map_inv, ha2]
    rw [h1]
    have h2 := hV (a (w : V))
    have h3 := hV (w : V)
    show (w : V) * (a (w : V))⁻¹ * (a (w : V) * (w : V)⁻¹)⁻¹ = 1
    have : (w : V) * (a (w : V))⁻¹ * (a (w : V) * (w : V)⁻¹)⁻¹ = (w : V) ^ 2 * ((a (w : V)) ^ 2)⁻¹ := by
      simp [sq, mul_comm, mul_left_comm, mul_assoc]
    rw [this, h2, h3]
    simp
  have hCker : (C.subgroupOf W) ≤ f.ker := by
    intro c hc
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [commHom_apply]
    have hc' : (c : V) ∈ C := hc
    show a (c : V) * (c : V)⁻¹ = 1
    rw [hCfix _ hc']
    simp
  have hθker : θ.ker = C.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, hθk]
    rfl
  have hx_ker : x ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [commHom_apply]
    show a (x : V) * (x : V)⁻¹ = 1
    have : a (x : V) = x := hx
    rw [this]
    simp
  have hθS : ∀ w : ↥W, θ (f w) = Multiplicative.ofAdd (muF2 3 γ (Multiplicative.toAdd (θ w)) -
      Multiplicative.toAdd (θ w)) := by
    intro w
    have h1 : f w = ⟨a w, hW w w.2⟩ * w⁻¹ := by
      apply Subtype.ext
      rfl
    rw [h1, map_mul, map_inv, hγ]
    apply Multiplicative.toAdd.injective
    simp [sub_eq_add_neg]
    rfl
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card ↥W := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card ↥(f.ker.map θ) * Nat.card ↥C = Nat.card f.ker := by
    have h3 := Subgroup.relIndex_mul_card θ.ker f.ker
    rw [Subgroup.relIndex_ker, inf_eq_left.2 (hθker ▸ hCker)] at h3
    rw [← h3, hθker]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCW).toEquiv).symm
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have h8 : Nat.card ↥(f.ker.map θ) * Nat.card f.range = 8 := by
    have : (Nat.card ↥(f.ker.map θ) * Nat.card f.range) * Nat.card ↥C = 8 * Nat.card ↥C := by
      calc (Nat.card ↥(f.ker.map θ) * Nat.card f.range) * Nat.card ↥C
          = (Nat.card ↥(f.ker.map θ) * Nat.card ↥C) * Nat.card f.range := by ring
        _ = Nat.card f.ker * Nat.card f.range := by rw [h2]
        _ = 8 * Nat.card ↥C := by rw [h1, hcard]
    exact Nat.eq_of_mul_eq_mul_right hCpos this
  obtain ⟨n, hn⟩ := exists_move γ hγ1
  obtain ⟨w, hw⟩ := hθs (Multiplicative.ofAdd n)
  have hlow : 2 ≤ Nat.card ↥(f.range.map θ) := by
    have hne : f.range.map θ ≠ ⊥ := by
      intro hbot
      have hmem : θ (f w) ∈ f.range.map θ := ⟨f w, ⟨w, rfl⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot, hθS, hw] at hmem
      apply hn
      have := congrArg Multiplicative.toAdd hmem
      simp only [toAdd_ofAdd, toAdd_one] at this
      exact sub_eq_zero.1 this
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hlt : f.range.map θ < f.ker.map θ := by
    refine lt_of_le_of_ne (Subgroup.map_mono hSKr) fun heq => ?_
    have hmem : θ x ∈ f.ker.map θ := ⟨x, hx_ker, rfl⟩
    rw [← heq] at hmem
    obtain ⟨s, ⟨w', rfl⟩, hs⟩ := hmem
    rw [hθS] at hs
    exact hxθ (Multiplicative.toAdd (θ w')) (by
      have := congrArg Multiplicative.toAdd hs
      simp only [toAdd_ofAdd] at this
      exact this.symm)
  have hge : 2 * Nat.card ↥(f.range.map θ) ≤ Nat.card ↥(f.ker.map θ) := by
    obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hlt.le
    have ht0 : t ≠ 0 := by
      rintro rfl
      have : 0 < Nat.card ↥(f.ker.map θ) := Nat.card_pos
      omega
    have ht1 : t ≠ 1 := by
      rintro rfl
      apply hlt.ne
      exact Subgroup.eq_of_le_of_card_ge hlt.le (by omega)
    rw [ht]
    nlinarith [Nat.pos_of_ne_zero ht0, (by omega : 2 ≤ t)]
  have h4 : 4 ≤ Nat.card ↥(f.ker.map θ) := by omega
  have : 4 * Nat.card f.range ≤ 8 := by
    calc 4 * Nat.card f.range ≤ Nat.card ↥(f.ker.map θ) * Nat.card f.range :=
          Nat.mul_le_mul_right _ h4
      _ = 8 := h8
  omega

@[expose] def invGens : Fin 3 → SL3F2 :=
  ![gens3 0,
    ⟨!![1, 0, 0; 1, 0, 1; 1, 1, 0], by simp [det_fin_three]; decide⟩,
    ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by simp [det_fin_three]⟩]

theorem invGens_sq : ∀ i, invGens i * invGens i = 1 := by decide +kernel

theorem invGens_ne : ∀ i, invGens i ≠ 1 := by decide +kernel

theorem wordEval_invGens : wordEval invGens [0, 2, 1, 0, 2, 0] = gens3 1 := by decide +kernel

theorem closure_invGens
    : Subgroup.closure (Set.range invGens) = ⊤ := by
  rw [eq_top_iff, ← closure_gens3]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · show gens3 1 ∈ _
    rw [← wordEval_invGens]
    exact wordEval_mem_closure invGens _

section Perfect

variable {V : Type} [CommGroup V]

theorem commutator_mem_commLeSub {W : Subgroup V} {X : Subgroup (MulAut V)}
    (hc : ∀ g ∈ X, ∀ v : V, g v * v⁻¹ ∈ W) {a b : MulAut V}
    (ha : a ∈ X) (hb : b ∈ X) : a * b * a⁻¹ * b⁻¹ ∈ B19.commLeSub (commSub W X) := by
  intro v
  set v₀ : V := (a⁻¹ * b⁻¹ : MulAut V) v with hv₀
  have hv : (b * a : MulAut V) v₀ = v := by
    rw [hv₀]; simp [MulAut.mul_apply]
  have h1 : (a * b * a⁻¹ * b⁻¹ : MulAut V) v = a (b v₀) := by
    rw [← hv]
    simp [MulAut.mul_apply]
  have h2 : (a * b * a⁻¹ * b⁻¹ : MulAut V) v * v⁻¹ = (a (b v₀) * (b (a v₀))⁻¹) := by
    rw [h1, ← hv]
    simp [MulAut.mul_apply]
  rw [h2]
  set p : V := b v₀ * v₀⁻¹ with hp
  set q : V := a v₀ * v₀⁻¹ with hq
  have hpW : p ∈ W := hc b hb v₀
  have hqW : q ∈ W := hc a ha v₀
  have e1 : a (b v₀) = (a p * p⁻¹) * p * a v₀ := by
    have : b v₀ = p * v₀ := by simp [hp]
    rw [this, map_mul]
    simp [mul_comm]
  have e2 : b (a v₀) = (b q * q⁻¹) * q * b v₀ := by
    have : a v₀ = q * v₀ := by simp [hq]
    rw [this, map_mul]
    simp [mul_comm]
  have e3 : a v₀ = q * v₀ := by simp [hq]
  have e4 : b v₀ = p * v₀ := by simp [hp]
  have hA : a p * p⁻¹ ∈ commSub W X := Subgroup.subset_closure ⟨a, ha, p, hpW, rfl⟩
  have hB : b q * q⁻¹ ∈ commSub W X := Subgroup.subset_closure ⟨b, hb, q, hqW, rfl⟩
  have e5 : a (b v₀) * (b (a v₀))⁻¹ = (a p * p⁻¹) * (b q * q⁻¹)⁻¹ := by
    rw [e1, e2, e3, e4]
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [e5]
  exact (commSub W X).mul_mem hA ((commSub W X).inv_mem hB)

theorem commV_le_commSub_of_perfect {W : Subgroup V} {X : Subgroup (MulAut V)} (hperf : ⁅X, X⁆ = X)
    (hc : ∀ g ∈ X, ∀ v : V, g v * v⁻¹ ∈ W) :
    commV X ≤ commSub W X := by
  rw [B19.commV_le_iff]
  intro g hg
  have hX : X ≤ B19.commLeSub (commSub W X) := by
    conv_lhs => rw [← hperf]
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact commutator_mem_commLeSub hc ha hb
  exact hX hg

end Perfect

section Join

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_sup_le_mul {M : Type*} [CommGroup M] (A B : Subgroup M) [Finite M] :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have h := card_sup_mul_card_inf A B
  have : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  nlinarith

theorem card_commSub_le_eight
    {W : Subgroup V} {G₂ : Subgroup (MulAut V)}
    (hGW : ∀ g ∈ G₂, ∀ w ∈ W, g w ∈ W) (ρ : SL3F2 →* ↥G₂) (hρ : Function.Surjective ρ)
    (hcard : ∀ i, Nat.card (commHom W (ρ (invGens i) : MulAut V)
      (hGW _ (ρ (invGens i)).2)).range ≤ 2) : Nat.card ↥(commSub W G₂) ≤ 8 := by
  set S : Fin 3 → Subgroup ↥W := fun i => (commHom W (ρ (invGens i) : MulAut V)
      (hGW _ (ρ (invGens i)).2)).range with hS
  set M : Subgroup ↥W := S 0 ⊔ S 1 ⊔ S 2 with hM
  set Mv : Subgroup V := M.map W.subtype with hMv
  let T : Subgroup (MulAut V) :=
    { carrier := {g | (∀ w ∈ W, g w ∈ W) ∧ (∀ w ∈ W, g⁻¹ w ∈ W) ∧ ∀ w ∈ W, g w * w⁻¹ ∈ Mv}
      one_mem' := ⟨fun w hw => hw, fun w hw => hw, fun w _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
        refine ⟨fun w hw => hg1 _ (hh1 w hw), fun w hw => ?_, fun w hw => ?_⟩
        · have : (g * h)⁻¹ w = h⁻¹ (g⁻¹ w) := by simp [_root_.mul_inv_rev, MulAut.mul_apply]
          rw [this]
          exact hh2 _ (hg2 w hw)
        · have : (g * h) w * w⁻¹ = (g (h w) * (h w)⁻¹) * (h w * w⁻¹) := by
            simp [MulAut.mul_apply, mul_comm, mul_left_comm, mul_assoc]
          rw [this]
          exact Mv.mul_mem (hg3 _ (hh1 w hw)) (hh3 w hw)
      inv_mem' := by
        rintro g ⟨hg1, hg2, hg3⟩
        refine ⟨hg2, fun w hw => by simpa using hg1 w hw, fun w hw => ?_⟩
        have h1 : g⁻¹ w * w⁻¹ = (g (g⁻¹ w) * (g⁻¹ w)⁻¹)⁻¹ := by
          have : g (g⁻¹ w) = w := by simp
          rw [this]
          simp
        rw [h1]
        exact Mv.inv_mem (hg3 _ (hg2 w hw)) }
  have hTi : ∀ i, ((ρ (invGens i) : ↥G₂) : MulAut V) ∈ T := by
    intro i
    have hgi := (ρ (invGens i)).2
    refine ⟨hGW _ hgi, fun w hw => hGW _ (G₂.inv_mem hgi) w hw, fun w hw => ?_⟩
    have hmem : commHom W (ρ (invGens i) : MulAut V) (hGW _ hgi) ⟨w, hw⟩ ∈ S i := ⟨⟨w, hw⟩, rfl⟩
    have hS' : S i ≤ M := by
      fin_cases i
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    exact ⟨_, hS' hmem, rfl⟩
  have hT : ∀ g ∈ G₂, g ∈ T := by
    have h1 : T.comap (G₂.subtype.comp ρ) = ⊤ := by
      rw [eq_top_iff, ← closure_invGens, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hTi i
    intro g hg
    obtain ⟨γ, hγ⟩ := hρ ⟨g, hg⟩
    have : γ ∈ T.comap (G₂.subtype.comp ρ) := by rw [h1]; trivial
    have h2 : ((ρ γ : ↥G₂) : MulAut V) ∈ T := this
    rw [hγ] at h2
    exact h2
  have hle : commSub W G₂ ≤ Mv := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, w, hw, rfl⟩
    exact (hT g hg).2.2 w hw
  calc Nat.card ↥(commSub W G₂) ≤ Nat.card ↥Mv := Subgroup.card_le_of_le hle
    _ = Nat.card ↥M := Subgroup.card_map_of_injective W.subtype_injective
    _ ≤ 8 := by
      calc Nat.card ↥M ≤ Nat.card ↥(S 0 ⊔ S 1) * Nat.card ↥(S 2) := card_sup_le_mul _ _
        _ ≤ (Nat.card ↥(S 0) * Nat.card ↥(S 1)) * Nat.card ↥(S 2) :=
            Nat.mul_le_mul_right _ (card_sup_le_mul _ _)
        _ ≤ (2 * 2) * 2 := Nat.mul_le_mul (Nat.mul_le_mul (hcard 0) (hcard 1)) (hcard 2)

end Join

section Dich

variable {V : Type} [CommGroup V]

theorem perfect_of_natQuot3 {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : NatQuot3 L U Z) :
    ⁅L, L⁆ = L := by
  have hp : Group.IsPerfect SL3F2 :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2) (n := 3) (le_refl 3)
  have : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := D.ρ) D.surj
  exact Subgroup.isPerfect_iff.mp this

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem l3_dichotomy [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (D : NatQuot3 G₂ (fixV G₁) (fixV G)) (hV₂ : fixV G₁ = commV G₂ ⊔ fixV G)
    (hcard : Nat.card ↥(fixV G₁) = 8 * Nat.card ↥(fixV G)) (u : V) :
    (∃ m : Additive ↥(fixV G₁), ∀ g : ↥G₂,
      ((Additive.toMul (cocyF h.hc₂ u g - (muW h.hLW₂ g m - m)) : ↥(fixV G₁)) : V) ∈ fixV G) ∨
      commV G₂ ⊓ fixV G = ⊥ := by
  let θa : Additive ↥(fixV G₁) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun w => Multiplicative.toAdd (D.θ (Additive.toMul w))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hθa : ∀ γ w, θa (muW h.hLW₂ (D.ρ γ) w) = muF2 3 γ (θa w) := by
    intro γ w
    have h1 := D.equiv γ (Additive.toMul w)
    show Multiplicative.toAdd (D.θ (Additive.toMul (muW h.hLW₂ (D.ρ γ) w))) =
      muF2 3 γ (Multiplicative.toAdd (D.θ (Additive.toMul w)))
    rw [muW_apply]
    exact congrArg Multiplicative.toAdd h1
  have hθs : Function.Surjective θa := by
    intro v
    obtain ⟨y, hy⟩ := D.θ_surj (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul y, by
      show Multiplicative.toAdd (D.θ y) = v
      rw [hy]; rfl⟩
  have hker : ∀ w, θa w = 0 → ((Additive.toMul w : ↥(fixV G₁)) : V) ∈ fixV G := fun w hw =>
    (D.θ_ker _).1 (Multiplicative.toAdd.injective hw)
  have hzZ : cocyF h.hc₂ u ∈ Z1A (muW h.hLW₂) := cocyF_mem_Z1A h.hLW₂ h.hc₂ u
  have hF : (fun γ => θa (cocyF h.hc₂ u (D.ρ γ))) ∈ Z1A (muF2 3) := by
    intro γ δ
    show θa (cocyF h.hc₂ u (D.ρ (γ * δ))) = θa (cocyF h.hc₂ u (D.ρ γ)) +
      muF2 3 γ (θa (cocyF h.hc₂ u (D.ρ δ)))
    rw [map_mul, hzZ, map_add, hθa]
  rcases Z1A_three_cases hF with hB | hB
  · left
    obtain ⟨m, hm⟩ := coboundary_mod_of_image h.hLW₂ D.ρ D.surj (muF2 3) θa hθs hθa hB
    exact ⟨m, fun g => hker _ (hm g)⟩
  · right
    obtain ⟨n₀, hn₀⟩ := hB
    have hn₀' : ∀ γ, θa (cocyF h.hc₂ u (D.ρ γ)) - cocycle3 γ = muF2 3 γ n₀ - n₀ := fun γ =>
      (congrFun hn₀ γ).symm
    have hCfix : ∀ i, ∀ c ∈ fixV G, ((D.ρ (invGens i) : ↥G₂) : MulAut V) c = c := fun i c hc =>
      hc _ (h.G₂_le (D.ρ (invGens i)).2)
    have hCW : fixV G ≤ fixV G₁ := B1.fixV_le_fixV h.G₁_le
    have hsqMul : ∀ i v, ((D.ρ (invGens i) : ↥G₂) : MulAut V)
        (((D.ρ (invGens i) : ↥G₂) : MulAut V) v) = v := by
      intro i v
      have h1 : D.ρ (invGens i) * D.ρ (invGens i) = 1 := by rw [← map_mul, invGens_sq, map_one]
      have := congrArg (fun g : ↥G₂ => (g : MulAut V) v) h1
      simpa using this
    have hcardS : ∀ i, Nat.card (commHom (fixV G₁) ((D.ρ (invGens i) : ↥G₂) : MulAut V)
        (h.hLW₂ _ (D.ρ (invGens i)).2)).range ≤ 2 := by
      intro i
      set a : MulAut V := ((D.ρ (invGens i) : ↥G₂) : MulAut V) with ha
      set x : ↥(fixV G₁) := Additive.toMul (cocyF h.hc₂ u (D.ρ (invGens i))) with hx
      have hxv : (x : V) = a u * u⁻¹ := rfl
      have hax : a (x : V) = (x : V) := by
        rw [hxv, map_mul, map_inv, hsqMul i u]
        have h1 : (a u * u⁻¹) * (a u * u⁻¹) = 1 := by
          have := hV (a u * u⁻¹)
          rwa [sq] at this
        have h2 : u * (a u)⁻¹ = (a u * u⁻¹)⁻¹ := by simp [mul_comm]
        rw [h2]
        exact inv_eq_of_mul_eq_one_right h1
      refine card_commHom_le_two hV (h.hLW₂ _ (D.ρ (invGens i)).2) (hsqMul i) hCW D.θ D.θ_surj
        D.θ_ker (hCfix i) hcard (invGens_ne i) (fun w => D.equiv (invGens i) w) (x := x) hax ?_
      intro n hn
      have h1 : θa (cocyF h.hc₂ u (D.ρ (invGens i))) = muF2 3 (invGens i) n - n := hn
      apply cocycle3_invol (invGens i) (invGens_sq i) (invGens_ne i) (n - n₀)
      have h2 := hn₀' (invGens i)
      rw [h1] at h2
      rw [map_sub]
      have h3 : cocycle3 (invGens i) = muF2 3 (invGens i) n - n - (muF2 3 (invGens i) n₀ - n₀) := by
        rw [← h2]; abel
      rw [h3]
      abel
    have h8 := card_commSub_le_eight h.hLW₂ D.ρ D.surj hcardS
    have hperf := perfect_of_natQuot3 D
    have hcomm : commV G₂ = commSub (fixV G₁) G₂ := by
      refine le_antisymm (commV_le_commSub_of_perfect hperf h.hc₂) ?_
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    have hcs := card_sup_mul_card_inf (commV G₂) (fixV G)
    rw [← hV₂, hcard] at hcs
    have hCpos : 0 < Nat.card ↥(fixV G) := Nat.card_pos
    have hk : Nat.card ↥(commV G₂ ⊓ fixV G) = 1 := by
      have hpos : 0 < Nat.card ↥(commV G₂ ⊓ fixV G) := Nat.card_pos
      have hle : Nat.card ↥(commV G₂) ≤ 8 := hcomm ▸ h8
      by_contra hne
      have h2 : 2 ≤ Nat.card ↥(commV G₂ ⊓ fixV G) := by omega
      have : 8 * Nat.card ↥(fixV G) * 2 ≤ Nat.card ↥(commV G₂) * Nat.card ↥(fixV G) := by
        calc 8 * Nat.card ↥(fixV G) * 2 ≤ 8 * Nat.card ↥(fixV G) * Nat.card ↥(commV G₂ ⊓ fixV G) :=
              Nat.mul_le_mul_left _ h2
          _ = Nat.card ↥(commV G₂) * Nat.card ↥(fixV G) := hcs
      nlinarith
    exact Subgroup.card_eq_one.1 hk

end B510Fa

end Dich

end Count

end FFC

end CFSG.Quasithin
