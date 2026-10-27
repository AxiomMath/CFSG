module

public import CFSG.Quasithin.Background.F918Z8Sz6Fb
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.F918J3
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin.SzTorus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.Ree

section Generic

variable {Y : Type} [CommGroup Y]

theorem card_isSylowTwoOf {G : Type*} [Group G] {Λ P : Subgroup G} (hPΛ : P ≤ Λ) {j m : ℕ}
    (hP : Nat.card ↥P = 2 ^ j) (hΛ : Nat.card ↥Λ = 2 ^ j * m) (hm : Odd m) :
    IsSylowTwoOf P Λ := by
  refine ⟨hPΛ, IsPGroup.of_card hP, ?_⟩
  have h1 := Subgroup.card_mul_index (P.subgroupOf Λ)
  have h2 : Nat.card ↥(P.subgroupOf Λ) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΛ).toEquiv
  rw [h2, hP, hΛ] at h1
  have h3 : (P.subgroupOf Λ).index = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [h3]
  exact Odd.not_two_dvd_nat hm

theorem odd_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h2 : 0 < 2 ^ m := Nat.two_pow_pos _
  obtain ⟨r, hr⟩ : Even (2 ^ m) := Nat.even_pow.2 ⟨even_two, by omega⟩
  exact ⟨r - 1, by omega⟩

theorem odd_cofactor (a : ℕ) :
    Odd ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) := by
  refine (odd_two_pow_sub_one (by omega)).mul ?_
  have : Even ((2 ^ (2 * a + 1)) ^ 2) :=
    Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by omega⟩
  exact this.add_one

@[expose] def szConj (z : MulAut Y) (Q : Subgroup (MulAut Y)) : Subgroup (MulAut Y) :=
  Q.map (MulAut.conj z).toMonoidHom

theorem mem_szConj {z : MulAut Y} {Q : Subgroup (MulAut Y)} {y : MulAut Y} :
    y ∈ szConj z Q ↔ z⁻¹ * y * z ∈ Q := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    show z⁻¹ * (z * q * z⁻¹) * z ∈ Q
    have : z⁻¹ * (z * q * z⁻¹) * z = q := by group
    rw [this]
    exact hq
  · intro h
    refine ⟨z⁻¹ * y * z, h, ?_⟩
    show z * (z⁻¹ * y * z) * z⁻¹ = y
    group

theorem isSylowTwoOf_szConj {Λ P : Subgroup (MulAut Y)} {z : MulAut Y}
    (hz : ∀ l ∈ Λ, z * l * z⁻¹ ∈ Λ) {j m : ℕ} (hPΛ : P ≤ Λ) (hP : Nat.card ↥P = 2 ^ j)
    (hΛ : Nat.card ↥Λ = 2 ^ j * m) (hm : Odd m) : IsSylowTwoOf (szConj z P) Λ := by
  refine card_isSylowTwoOf (j := j) ?_ ?_ hΛ hm
  · rintro _ ⟨p, hp, rfl⟩
    exact hz p (hPΛ hp)
  · rw [szConj, Subgroup.card_map_of_injective (MulAut.conj z).injective, hP]

end Generic

section Coord

variable {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)} {V : Subgroup Y}

structure SzCoord (Λ : Subgroup (MulAut Y)) (V : Subgroup Y) (a : ℕ) (K : Type) [Field K] where
  inv : ∀ l ∈ Λ, ∀ v ∈ V, l v ∈ V
  θ : ↥Λ ≃* ↥(suzukiGroup a K)
  Θ : ↥V ≃* Multiplicative (Fin 4 → K)
  equivar : ∀ (l : ↥Λ) (v : ↥V),
    Θ ⟨(l : MulAut Y) (v : Y), inv _ l.2 _ v.2⟩ = natAct (suzukiGroup a K) (θ l) (Θ v)

theorem szCoord_of_natural (hLV : Λ ≤ stabSub V) (hfaith : Λ ⊓ centSub V = ⊥) {f : ℕ}
    (h : BinaryNaturalSz (autSub Λ V) ⊤ ⊥ f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K), f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧
      Nonempty (SzCoord Λ V a K) := by
  obtain ⟨a, ha, hfa, K, _, _, hc, π, hπ⟩ := h
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.nat (suzukiGroup a K)) rfl hπ
  let Θ : ↥V ≃* Multiplicative (Fin 4 → K) := E.trans Subgroup.topEquiv
  have hΘ : ∀ (γ : ↥(suzukiGroup a K)) (v : ↥V),
      Θ (((π γ : ↥(autSub Λ V)) : MulAut ↥V) v) = natAct (suzukiGroup a K) γ (Θ v) :=
    fun γ v => hE γ v
  have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
  let e : ↥(suzukiGroup a K) ≃* ↥(autSub Λ V) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  let ρ : ↥Λ ≃* ↥(autSub Λ V) := autSubEquivOfFaithful hLV hfaith
  refine ⟨a, K, inferInstance, inferInstance, hfa, hc,
    ⟨⟨fun l hl v hv => (hLV hl v).2 hv, ρ.trans e.symm, Θ, fun l v => ?_⟩⟩⟩
  have hπl : π (e.symm (ρ l)) = ρ l := e.apply_symm_apply (ρ l)
  have h1 := hΘ (e.symm (ρ l)) v
  rw [hπl] at h1
  have h2 : ((ρ l : ↥(autSub Λ V)) : MulAut ↥V) v =
      ⟨(l : MulAut Y) (v : Y), (hLV l.2 v).2 v.2⟩ :=
    Subtype.ext (by
      rw [show ((ρ l : ↥(autSub Λ V)) : MulAut ↥V) = resHomOn V hLV l from
        autSubEquivOfFaithful_apply hLV hfaith l]
      rfl)
  rw [h2] at h1
  exact h1

end Coord

section Sylow

variable {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)} {V : Subgroup Y}
  {a : ℕ} {K : Type} [Field K] [Finite K]

@[expose] noncomputable def SzCoord.P (C : SzCoord Λ V a K) : Subgroup (MulAut Y) :=
  (suzukiU a K).map (Λ.subtype.comp C.θ.symm.toMonoidHom)

omit [Finite K] in
theorem SzCoord.mem_P_iff (C : SzCoord Λ V a K) (l : ↥Λ) :
    (l : MulAut Y) ∈ C.P ↔ C.θ l ∈ suzukiU a K := by
  constructor
  · rintro ⟨g, hg, hgl⟩
    have : C.θ.symm g = l := Subtype.ext hgl
    rw [← this, MulEquiv.apply_symm_apply]
    exact hg
  · intro h
    exact ⟨C.θ l, h, by simp⟩

omit [Finite K] in
theorem SzCoord.P_le (C : SzCoord Λ V a K) : C.P ≤ Λ := by
  rintro _ ⟨g, -, rfl⟩
  exact (C.θ.symm g).2

theorem SzCoord.card_P (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card ↥C.P = (2 ^ (2 * a + 1)) ^ 2 := by
  have hinj : Function.Injective (Λ.subtype.comp C.θ.symm.toMonoidHom) :=
    Subtype.val_injective.comp C.θ.symm.injective
  rw [SzCoord.P, Subgroup.card_map_of_injective hinj]
  exact (suzuki_unipotent_structure hK).2.1

theorem SzCoord.card_Lam (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card ↥Λ = 2 ^ (2 * (2 * a + 1)) *
      ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) := by
  rw [Nat.card_congr C.θ.toEquiv, suzuki_order hK, ← mul_assoc, ← pow_mul,
    mul_comm (2 * a + 1) 2]

theorem SzCoord.isSylowTwoOf_P (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSylowTwoOf C.P Λ :=
  card_isSylowTwoOf C.P_le (j := 2 * (2 * a + 1))
    (by rw [C.card_P hK, ← pow_mul, mul_comm (2 * a + 1) 2]) (C.card_Lam hK) (odd_cofactor a)

omit [Finite K] in
theorem SzCoord.mem_fix_P_iff (C : SzCoord Λ V a K) (v : ↥V) :
    (v : Y) ∈ fixV C.P ↔ C.Θ v ∈ natFix a K (suzukiU a K) := by
  constructor
  · intro hv g hg
    have hl : ((C.θ.symm g : ↥Λ) : MulAut Y) ∈ C.P :=
      (C.mem_P_iff _).2 (by simpa using hg)
    have h1 : ((C.θ.symm g : ↥Λ) : MulAut Y) (v : Y) = (v : Y) := hv _ hl
    have h2 := C.equivar (C.θ.symm g) v
    rw [MulEquiv.apply_symm_apply] at h2
    rw [← h2]
    congr 1
    exact Subtype.ext h1
  · intro hv p hp
    have hpΛ : p ∈ Λ := C.P_le hp
    have h1 := (C.mem_P_iff ⟨p, hpΛ⟩).1 hp
    have h2 := C.equivar ⟨p, hpΛ⟩ v
    rw [hv _ h1] at h2
    have h3 := C.Θ.injective h2
    exact congrArg Subtype.val h3

theorem SzCoord.card_fix_P (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card ↥(V ⊓ fixV C.P) = 2 ^ (2 * a + 1) := by
  rw [← natFix_suzukiU_card hK]
  refine Nat.card_congr (Equiv.ofBijective
    (fun v : ↥(V ⊓ fixV C.P) => (⟨C.Θ ⟨v, v.2.1⟩, (C.mem_fix_P_iff ⟨v, v.2.1⟩).1 v.2.2⟩ :
      ↥(natFix a K (suzukiU a K)))) ⟨?_, ?_⟩)
  · intro x y hxy
    have h0 := congrArg (fun z : ↥(natFix a K (suzukiU a K)) => z.1) hxy
    have h1 := C.Θ.injective h0
    exact Subtype.ext (congrArg (fun z : ↥V => (z : Y)) h1)
  · rintro ⟨w, hw⟩
    refine ⟨⟨(C.Θ.symm w : Y), (C.Θ.symm w).2, ?_⟩, ?_⟩
    · exact (C.mem_fix_P_iff (C.Θ.symm w)).2 (by simpa using hw)
    · apply Subtype.ext
      simp

omit [Finite K] in
theorem SzCoord.normalizer_P (C : SzCoord Λ V a K) {s : MulAut Y} (hsΛ : s ∈ Λ)
    (hsN : s ∈ Subgroup.normalizer (C.P : Set (MulAut Y))) :
    C.θ ⟨s, hsΛ⟩ ∈ Subgroup.normalizer (suzukiU a K : Set ↥(suzukiGroup a K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  obtain ⟨l, rfl⟩ := C.θ.surjective g
  have e1 : C.θ ⟨s, hsΛ⟩ * C.θ l * (C.θ ⟨s, hsΛ⟩)⁻¹ = C.θ (⟨s, hsΛ⟩ * l * ⟨s, hsΛ⟩⁻¹) := by
    simp [map_mul, map_inv]
  rw [e1, ← C.mem_P_iff, ← C.mem_P_iff]
  have := Subgroup.mem_normalizer_iff.1 hsN (l : MulAut Y)
  simpa using this

omit [Finite K] in
theorem SzCoord.mem_normalizer_P (C : SzCoord Λ V a K) {s : MulAut Y} (hsΛ : s ∈ Λ)
    (hs : C.θ ⟨s, hsΛ⟩ ∈ Subgroup.normalizer (suzukiU a K : Set ↥(suzukiGroup a K))) :
    s ∈ Subgroup.normalizer (C.P : Set (MulAut Y)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ Λ
  · set σ : ↥Λ := ⟨s, hsΛ⟩ with hσ
    set l : ↥Λ := ⟨y, hy⟩ with hl
    have h1 := Subgroup.mem_normalizer_iff.1 hs (C.θ l)
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    show (l : MulAut Y) ∈ C.P ↔ ((σ * l * σ⁻¹ : ↥Λ) : MulAut Y) ∈ C.P
    exact (C.mem_P_iff l).trans (h1.trans (C.mem_P_iff (σ * l * σ⁻¹)).symm)
  · have h1 : y ∉ C.P := fun h => hy (C.P_le h)
    have h2 : s * y * s⁻¹ ∉ C.P := fun h => hy (by
      have := Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hsΛ) (C.P_le h)) hsΛ
      simpa [mul_assoc] using this)
    exact iff_of_false h1 h2

theorem SzCoord.fix_zpowers_eq_bot (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {s : MulAut Y} (hsΛ : s ∈ Λ) (hsN : s ∈ Subgroup.normalizer (C.P : Set (MulAut Y)))
    (hord : orderOf s = 2 ^ (2 * a + 1) - 1) {k : ℕ} (hk : ¬ (2 ^ (2 * a + 1) - 1 ∣ k)) :
    V ⊓ fixV C.P ⊓ fixV (Subgroup.zpowers (s ^ k)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
  obtain ⟨⟨hyV, hyP⟩, hyZ⟩ := hy
  have hordγ : orderOf (C.θ ⟨s, hsΛ⟩) = 2 ^ (2 * a + 1) - 1 := by
    rw [← hord]
    have h1 := orderOf_injective C.θ.toMonoidHom C.θ.injective (⟨s, hsΛ⟩ : ↥Λ)
    refine h1.trans ?_
    exact (Subgroup.orderOf_coe (⟨s, hsΛ⟩ : ↥Λ)).symm
  have hx := (natFix_suzukiU_eq hK _).1 ((C.mem_fix_P_iff ⟨y, hyV⟩).1 hyP)
  have hfix : natAct (suzukiGroup a K) (C.θ ⟨s, hsΛ⟩ ^ k) (C.Θ ⟨y, hyV⟩) = C.Θ ⟨y, hyV⟩ := by
    have h1 := C.equivar ((⟨s, hsΛ⟩ : ↥Λ) ^ k) ⟨y, hyV⟩
    rw [← map_pow, ← h1]
    congr 1
    exact Subtype.ext (hyZ (s ^ k) (Subgroup.mem_zpowers _))
  have := natFix_pow_fix hK (C.normalizer_P hsΛ hsN) hordγ hk hx hfix
  have h2 : (⟨y, hyV⟩ : ↥V) = 1 := C.Θ.injective (by rw [this, map_one])
  exact congrArg Subtype.val h2

theorem SzCoord.exists_torus (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ t : MulAut Y, t ∈ Λ ∧ t ∈ Subgroup.normalizer (C.P : Set (MulAut Y)) ∧
      orderOf t = 2 ^ (2 * a + 1) - 1 := by
  obtain ⟨l₀, hl₀⟩ := exists_suzukiD_order (a := a) (K := K) hK
  refine ⟨((C.θ.symm (suzukiDElt a K l₀) : ↥Λ) : MulAut Y), (C.θ.symm _).2, ?_, ?_⟩
  · refine C.mem_normalizer_P (C.θ.symm _).2 ?_
    simpa using suzukiT_le_normalizer hK (suzukiDElt_mem_suzukiT a K l₀)
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hl₀]

end Sylow

end CFSG.Quasithin.SzTorus
