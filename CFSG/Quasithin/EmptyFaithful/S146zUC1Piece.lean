module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoDef
import CFSG.Quasithin.EmptyFaithful.S153QPC1
import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.S153M

namespace S146zU

@[expose] def L216Cover (L : Type) [Group L] : Prop :=
  Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))

namespace UC1

theorem card_of_L216Cover {L : Type} [Group L] (h : L216Cover L) : Nat.card L = 4080 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact QP.card_sl2_sixteen

theorem L216Cover_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : L216Cover L) : L216Cover L' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem L216Cover_map_conj {Γ : Type} [Group Γ] {L : Subgroup Γ} (τ : Γ) (h : L216Cover ↥L) :
    L216Cover ↥(L.map (MulAut.conj τ).toMonoidHom) :=
  L216Cover_of_mulEquiv
    (Subgroup.equivMapOfInjective L (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective) h

theorem L216Cover_of_surjective {X Y : Type} [Group X] [Group Y] [Nontrivial Y] (f : X →* Y)
    (hf : Function.Surjective f) {O : Subgroup X} [O.Normal] (hO : O ≤ f.ker)
    (e : Nonempty (X ⧸ O ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    L216Cover Y := by
  obtain ⟨eK⟩ := e
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
    QP.sl2_sixteen_isSimpleGroup
  have hsimple : IsSimpleGroup (X ⧸ O) := eK.isSimpleGroup
  let θ : X ⧸ O →* Y := QuotientGroup.lift O f hO
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨QuotientGroup.mk x, by simpa [θ] using hx⟩
  have hθi : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal θ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨x, rfl⟩ := hθs y
      exact hy (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
  exact ⟨(MulEquiv.ofBijective θ ⟨hθi, hθs⟩).symm.trans eK⟩

section Quad

variable {V : Type} [CommGroup V]

private theorem commV_apply_mem {A B : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {b : MulAut V} (hb : b ∈ B) {u : V}
    (hu : u ∈ commV A) : b u ∈ commV A := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have h1 : x (b v) = b (x v) := by
      have := congrArg (fun f : MulAut V => f v) (hcomm x hx b hb)
      simpa using this
    rw [map_mul, map_inv, ← h1]
    exact Subgroup.subset_closure ⟨x, hx, b v, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a c _ _ ha hc => rw [map_mul]; exact mul_mem ha hc
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

private theorem commV_le_fixV {L₁ L₂ : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hperf : Group.IsPerfect ↥L₂)
    {C W₁ W₂ : Subgroup V} (hC : C ≤ fixV L₂) (hW₁ : commV L₁ ≤ W₁) (hW₂ : commV L₂ ≤ W₂)
    (hCW : W₁ ⊓ W₂ ≤ C) : commV L₁ ≤ fixV L₂ := by
  intro u hu
  have hmem : ∀ b ∈ L₂, (b : MulAut V) u * u⁻¹ ∈ C := by
    intro b hb
    refine hCW ⟨hW₁ ?_, hW₂ (Subgroup.subset_closure ⟨b, hb, u, rfl⟩)⟩
    exact mul_mem (commV_apply_mem hcomm hb hu) (inv_mem hu)
  let f : ↥L₂ →* V :=
    { toFun := fun b => (b : MulAut V) u * u⁻¹
      map_one' := by simp
      map_mul' := fun b b' => by
        have hc : (b' : MulAut V) u * u⁻¹ ∈ fixV L₂ := hC (hmem b' b'.2)
        have h1 : (b : MulAut V) ((b' : MulAut V) u * u⁻¹) = (b' : MulAut V) u * u⁻¹ :=
          hc b b.2
        rw [map_mul, map_inv] at h1
        have h2 : (b : MulAut V) ((b' : MulAut V) u) =
            (b' : MulAut V) u * u⁻¹ * (b : MulAut V) u := mul_inv_eq_iff_eq_mul.1 h1
        show ((b : MulAut V) * (b' : MulAut V)) u * u⁻¹ = _
        rw [MulAut.mul_apply, h2]
        ac_rfl }
  have hker : ∀ b : ↥L₂, f b = 1 := by
    intro b
    have : b ∈ commutator ↥L₂ := by rw [hperf.commutator_eq_top]; trivial
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker f this)
  intro b hb
  have := hker ⟨b, hb⟩
  exact mul_inv_eq_one.1 this

end Quad

section Conj

variable {V : Type} [CommGroup V]

private theorem conj_apply' (τ a : MulAut V) (v : V) :
    ((MulAut.conj τ).toMonoidHom a) v = τ (a (τ⁻¹ v)) := by
  simp [MulAut.conj_apply]

private theorem commV_map {L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom) :
    (commV L₁).map τ.toMonoidHom = commV L₂ := by
  subst hτ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨a, ha, v, rfl⟩
    show τ (a v * v⁻¹) ∈ commV _
    have : τ (a v * v⁻¹) = ((MulAut.conj τ).toMonoidHom a) (τ v) * (τ v)⁻¹ := by
      rw [conj_apply', map_mul, map_inv]
      simp
    rw [this]
    exact Subgroup.subset_closure ⟨_, Subgroup.mem_map_of_mem _ ha, τ v, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨a (τ⁻¹ v) * (τ⁻¹ v)⁻¹, Subgroup.subset_closure ⟨a, ha, τ⁻¹ v, rfl⟩, ?_⟩
    show τ (a (τ⁻¹ v) * (τ⁻¹ v)⁻¹) = _
    rw [conj_apply', map_mul, map_inv]
    simp

end Conj

section Orders

private theorem card_statedSL_two {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

private theorem card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

private theorem card_statedSL_three_two {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    Nat.card ↥(StatedSL 3 K) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two h

end Orders

section Arith

private theorem two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b := by
  have hu' : ¬ 2 ∣ u := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hu
  have hw' : ¬ 2 ∣ w := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hw
  have h1 : padicValNat 2 (2 ^ a * u) = a := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hu.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu', add_zero]
  have h2 : padicValNat 2 (2 ^ b * w) = b := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hw.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hw', add_zero]
  rw [← h1, ← h2, h]

private theorem odd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k - 1) := by
  have h : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h odd_one

private theorem arith_sl3 {m : ℕ} (hm : 1 ≤ m)
    (h : (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) = 4080) : False := by
  have hw : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    (by rw [← pow_mul]; exact odd_two_pow_sub_one (by omega) :
        Odd ((2 ^ m) ^ 2 - 1)).mul
      (by rw [← pow_mul]; exact odd_two_pow_sub_one (by omega) : Odd ((2 ^ m) ^ 3 - 1))
  have h' : 2 ^ (m * 3) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) = 2 ^ 4 * 255 := by
    rw [pow_mul]
    omega
  have := two_pow_mul_odd_inj hw (by decide : Odd 255) h'
  omega

end Arith

section Excl

private theorem injective_of_faithful {V : Type} [CommGroup V] {D : FFModel}
    (hD : D.Faithful) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨-, -, -, hHU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  apply hD
  intro m hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hact : D.act γ m ∈ D.sec := hsec γ m hm
  have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
  have h1 := hβe γ u ⟨m, hm⟩ hu' hact hu
  have h2' : ((π γ : ↥H) : MulAut V) (u : V) = (u : V) := by rw [hγ]; rfl
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext h2'
  rw [h2, hu] at h1
  have h3 := QuotientGroup.eq.mp h1
  have h4 : m⁻¹ * D.act γ m ∈ D.ker := h3
  rw [mul_comm]
  exact h4

private theorem bijective_of_nat {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {ι : Type}
    [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {U Z : Subgroup V} {π : ↥Γ →* ↥L} (h : (FFModel.nat Γ).RealizesVia L U Z π) :
    Function.Bijective π :=
  ⟨injective_of_faithful (FFModel.nat_faithful Γ) h, h.1⟩

private theorem one_le_of_card_eq {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : Nat.card F = 2 ^ m) : 1 ≤ m := by
  by_contra h0
  obtain rfl : m = 0 := by omega
  have h1 := Finite.one_lt_card (α := F)
  rw [pow_zero] at hm
  omega

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

private theorem false_of_sl3 (hK : L216Cover ↥L) {F : Type}
    [Field F] [Finite F] {m : ℕ} (hm : Nat.card F = 2 ^ m) {U Z : Subgroup V}
    (h : (FFModel.nat (StatedSL 3 F)).Realizes L U Z) : False := by
  obtain ⟨π, hπ⟩ := h
  have hm1 : 1 ≤ m := one_le_of_card_eq hm
  let e : ↥(StatedSL 3 F) ≃* ↥L := MulEquiv.ofBijective π (bijective_of_nat hπ)
  have hc : Nat.card ↥(StatedSL 3 F) = 4080 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_of_L216Cover hK
  rw [card_statedSL_three, hm] at hc
  exact arith_sl3 hm1 hc

private theorem two_le_of_nat (hK : L216Cover ↥L) {F : Type}
    [Field F] [Finite F] {m : ℕ} (hm : Nat.card F = 2 ^ m) {U Z : Subgroup V}
    (h : (FFModel.nat (StatedSL 2 F)).Realizes L U Z) : 2 ≤ m := by
  by_contra hlt
  obtain ⟨π, hπ⟩ := h
  have h1 := Finite.one_lt_card (α := F)
  have hm2 : m < 2 := by omega
  interval_cases m
  · rw [pow_zero] at hm
    omega
  · have hF : Nat.card F = 2 := by simpa using hm
    have hc : Nat.card ↥L = 6 := by
      rw [← Nat.card_congr (Equiv.ofBijective π (bijective_of_nat hπ))]
      show Nat.card ↥(StatedSL 2 F) = 6
      rw [card_statedSL_two, hF]
      norm_num
    have := card_of_L216Cover hK
    omega

private theorem false_of_sym5 (hK : L216Cover ↥L)
    {U Z : Subgroup V} (h : SymmetricNatural L U Z 5) : False := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥L ≤ Nat.card (Equiv.Perm (Fin 5)) := Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have := card_of_L216Cover hK
  omega

private theorem false_of_sl3_two (hK : L216Cover ↥L)
    (e : Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := e
  have h1 : Nat.card ↥L = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_statedSL_three_two (Nat.card_zmod 2)
  have := card_of_L216Cover hK
  omega

private theorem piece {W C : Subgroup V} (hK : L216Cover ↥L) (h : B56Piece L W C) :
    W = commV L ⊔ C ∧ ∃ m, 2 ≤ m ∧ BinaryNaturalSL L (commV L ⊔ C) C 2 m := by
  rcases h with ⟨hW, h⟩ | ⟨hW, m, F, hF, hFin, hm, hd⟩ | ⟨e, -, -, -, -⟩
  · subst hW
    refine ⟨rfl, ?_⟩
    rcases h with ⟨n, F, hF, hFin, hn, hR⟩ | hS | ⟨m, F, hF, hFin, hm, hR⟩
    · exact ⟨n, two_le_of_nat hK hn hR, F, hF, hFin, hn, hR⟩
    · exact (false_of_sym5 hK hS).elim
    · exact (false_of_sl3 hK hm hR).elim
  · obtain ⟨I, π, -, -, -, hreal⟩ := hd
    exact (false_of_sl3 hK hm ⟨π, hreal ⟨0, by norm_num⟩⟩).elim
  · exact (false_of_sl3_two hK e).elim

end Excl

section Main

theorem twoNat_of_twoB56_L216 {V : Type} [CommGroup V] {X L₁ L₂ : Subgroup (MulAut V)}
    {τ : MulAut V} (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hK : L216Cover ↥L₁) (h : TwoB56 X L₁ L₂) :
    TwoNat L₁ L₂ τ := by
  obtain ⟨-, W₁, W₂, -, -, hsup, hinf, hp₁, hp₂⟩ := h
  let e : ↥L₁ ≃* ↥L₂ :=
    (Subgroup.equivMapOfInjective L₁ (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hτ.symm)
  have hK₂ : L216Cover ↥L₂ := L216Cover_of_mulEquiv e hK
  have hperf₁ : Group.IsPerfect ↥L₁ := hq₁.1
  have hperf₂ : Group.IsPerfect ↥L₂ :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hW₁, hn₁⟩ := piece hK hp₁
  obtain ⟨hW₂, hn₂⟩ := piece hK₂ hp₂
  have hc₁ : commV L₁ ≤ W₁ := hW₁ ▸ le_sup_left
  have hc₂ : commV L₂ ≤ W₂ := hW₂ ▸ le_sup_left
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hfix₂ : fixV (L₁ ⊔ L₂) ≤ fixV L₂ := fun v hv x hx => hv x (Subgroup.mem_sup_right hx)
  have hfix₁ : fixV (L₁ ⊔ L₂) ≤ fixV L₁ := fun v hv x hx => hv x (Subgroup.mem_sup_left hx)
  have hq₂ : commV L₁ ≤ fixV L₂ := commV_le_fixV hcomm hperf₂ hfix₂ hc₁ hc₂ hinf.le
  have hq₁' : commV L₂ ≤ fixV L₁ :=
    commV_le_fixV hcomm' hperf₁ hfix₁ hc₂ hc₁ (by rw [inf_comm]; exact hinf.le)
  have hmap := commV_map hτ
  unfold TwoNat
  refine ⟨hn₁, hn₂, ?_, ?_, ?_, hq₂, hq₁'⟩
  · rw [← hW₁, ← hW₂, hsup]
  · rw [← hW₁, ← hW₂, hinf]
  · have hsum : commV L₁ ⊔ commV L₂ ⊔ fixV (L₁ ⊔ L₂) = ⊤ := by
      rw [← hsup, hW₁, hW₂]
      ac_rfl
    unfold IsSumMod
    rw [hmap]
    exact ⟨hsum.symm, by rw [← hW₁, ← hW₂, hinf]⟩

end Main

end UC1

end S146zU

end CFSG.Quasithin
