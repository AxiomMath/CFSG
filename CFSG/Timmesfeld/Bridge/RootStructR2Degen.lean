module

public import CFSG.Timmesfeld.Bridge.RootStructR2DegenTorus
public import CFSG.Timmesfeld.Bridge.RootStructWTIFaithful

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity RootClosure

namespace RootDegen

theorem conj_iterate {G : Type*} [Group G] (g w : G) (n : ℕ) :
    (fun v => g * v * g⁻¹)^[n] w = g ^ n * w * (g ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    group

theorem map_conj_eq_of_forall {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (hg : ∀ u ∈ H, g * u * g⁻¹ ∈ H) : H.map (MulAut.conj g).toMonoidHom = H := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact hg u hu
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

namespace DegenConf

variable {G : Type} [Group G] {D : Set G} {a b x : G} (C : DegenConf D a b x)
include C

theorem commLambda : Moufang.CommLambda D :=
  have := C.finite
  commLambda_of_nCoreCommutatorInRoot C.isClass C.root
    (nCoreCommutatorInRoot_of_hyp C.hyp C.closure)

theorem isPGroup_rootGroup (d : G) (hd : d ∈ D) : IsPGroup 2 (rootGroup D d) :=
  OddLocal.isPGroup_two_of_mul_self fun _ hg => mul_self_eq_one_of_mem_rootGroup C.root hd hg

theorem four_le_card (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) :
    4 ≤ Nat.card (rootGroup D b) := by
  have := C.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, e, he, hne⟩ := hl
  rw [card_rootGroup_eq C.isClass C.root C.closure hd C.hb]
  have hsub : ({1, d, e} : Set G) ⊆ (rootGroup D d : Set G) := by
    intro w hw
    rcases hw with h | h | h
    · rw [h]
      exact (rootGroup D d).one_mem
    · rw [h]
      exact rootSet_subset_rootGroup D d (mem_rootSet_self hd)
    · rw [Set.mem_singleton_iff.1 h]
      exact rootSet_subset_rootGroup D d he
  have h3 : ({1, d, e} : Set G).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, d, e, (C.root.ne_one hd).symm, (C.root.ne_one he.1).symm, hne.symm, rfl⟩
  have hle : 3 ≤ Nat.card (rootGroup D d) := by
    rw [← h3, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (C.isPGroup_rootGroup d hd)
  rw [hk] at hle ⊢
  rcases k with _ | _ | k
  · norm_num at hle
  · norm_num at hle
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_torus (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) (h1 : OneOpposite D b x) :
    ∃ h₀ ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x, (orderOf h₀).Prime ∧
      orderOf h₀ ≠ 2 ∧ (∀ β ∈ rootGroup D b, h₀ * β * h₀⁻¹ ∈ rootGroup D b) ∧
      (∀ β ∈ rootGroup D b, h₀⁻¹ * β * h₀ ∈ rootGroup D b) ∧
      ∃ y ∈ D, y * h₀ * y⁻¹ = h₀⁻¹ := by
  have := C.finite
  have hD := C.root
  obtain ⟨n, hn, -, φ, hφx, hφb⟩ := exists_mulEquiv_SL2_of_oneOpposite C.hyp C.closure C.special
    C.commLambda C.hb C.hx C.hbx C.hoddbx h1 (C.four_le_card hl)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    exact (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  obtain ⟨p, hp, hp2, hT, hord, hlow, hlow', gT, -, uT, huT, huT1, hw⟩ :=
    exists_torus_weyl (F := GaloisField 2 n) hF
  have hX₀X : rootGroup D x ⊔ rootGroup D b ≤ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x :=
    sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hmemb : ∀ z : ↥(rootGroup D x ⊔ rootGroup D b),
      (z : G) ∈ rootGroup D b ↔ φ z ∈ lowerUnipotent (GaloisField 2 n) := by
    intro z
    rw [← hφb]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', hzz'⟩
      have := φ.injective hzz'
      rw [← this]
      exact hz'
  have horder : orderOf ((φ.symm hT : ↥(rootGroup D x ⊔ rootGroup D b)) : G) = p := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
  refine ⟨(φ.symm hT : G), hX₀X (φ.symm hT).2, horder ▸ hp, horder ▸ hp2, ?_, ?_, ?_⟩
  · intro β hβ
    have hβX₀ : β ∈ rootGroup D x ⊔ rootGroup D b := Subgroup.mem_sup_right hβ
    have h1' := hlow _ ((hmemb ⟨β, hβX₀⟩).1 hβ)
    have h2 : φ (φ.symm hT * ⟨β, hβX₀⟩ * (φ.symm hT)⁻¹) = hT * φ ⟨β, hβX₀⟩ * hT⁻¹ := by
      simp
    rw [← h2, ← hmemb] at h1'
    simpa using h1'
  · intro β hβ
    have hβX₀ : β ∈ rootGroup D x ⊔ rootGroup D b := Subgroup.mem_sup_right hβ
    have h1' := hlow' _ ((hmemb ⟨β, hβX₀⟩).1 hβ)
    have h2 : φ ((φ.symm hT)⁻¹ * ⟨β, hβX₀⟩ * φ.symm hT) = hT⁻¹ * φ ⟨β, hβX₀⟩ * hT := by
      simp
    rw [← h2, ← hmemb] at h1'
    simpa using h1'
  ·
    have hux : ((φ.symm uT : ↥(rootGroup D x ⊔ rootGroup D b)) : G) ∈ rootGroup D x := by
      rw [← hφx] at huT
      obtain ⟨z, hz, hzuT⟩ := huT
      have : φ.symm uT = z := by rw [← hzuT]; simp
      rw [this]
      exact hz
    have hu1 : ((φ.symm uT : ↥(rootGroup D x ⊔ rootGroup D b)) : G) ≠ 1 := by
      intro h'
      apply huT1
      have : φ.symm uT = 1 := Subtype.ext h'
      simpa using congrArg φ this
    have huD := (mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure C.hx hux hu1).1
    refine ⟨(φ.symm (gT * uT * gT⁻¹) : G), ?_, ?_⟩
    · have := C.conj_mem ((φ.symm gT : ↥(rootGroup D x ⊔ rootGroup D b)) : G) huD
      simpa using this
    · have := congrArg (fun z => ((φ.symm z : ↥(rootGroup D x ⊔ rootGroup D b)) : G)) hw
      simpa using this

theorem exists_fixed_line (h1 : OneOpposite D b x) {h₀ : G}
    (hh₀ : h₀ ∈ Subgroup.normalizer (rootGroup D b : Set G))
    (hh₀L : ∀ u ∈ rootGroup D b ⊔ rootGroup D a, h₀ * u * h₀⁻¹ ∈ rootGroup D b ⊔ rootGroup D a)
    (hp : (orderOf h₀).Prime) (hp2 : orderOf h₀ ≠ 2) :
    ∃ c ∈ D, Commute b c ∧ b * c ∈ D ∧ c ∉ rootSet D b ∧ c ∉ rootGroup D b ⊔ rootGroup D a ∧
      ∀ u ∈ rootGroup D b ⊔ rootGroup D c, h₀ * u * h₀⁻¹ ∈ rootGroup D b ⊔ rootGroup D c := by
  classical
  have := C.finite
  have hD := C.root
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (orderOf h₀).Prime := ⟨hp⟩
  have hLS : LineSetting G D :=
    ⟨C.hyp, C.closure, C.special, C.conn, ⟨b, C.hb, a, C.ha, C.hba, C.hbaD, C.haT, C.lineTI⟩⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hoff : ∀ {c : G}, c ∈ D → c ∉ rootSet D b →
      rootGroup D b ⊔ rootGroup D c ≠ rootGroup D b ⊔ rootGroup D a →
      c ∉ rootGroup D b ⊔ rootGroup D a := by
    intro c hc hcT hne hcL
    exact hne (sup_rootGroup_eq_of_mem C.hyp C.closure C.special C.hb C.ha C.hba C.hbaD C.haT
      C.b_mem_L hcL (hD.ne_one C.hb) (hD.ne_one hc) hcT)
  obtain ⟨e, he, hbe, hbeD, h4⟩ := h1
  have heT : e ∉ rootSet D b := by
    intro heT
    have h4' : orderOf (e * x) = 4 := by rwa [orderOf_mul_comm_eq]
    have h4b := (orderOf_mul_eq_four_iff_of_mem_rootSet hD C.hb heT C.hx).1 h4'
    have hodd := C.hoddbx
    rw [h4b] at hodd
    exact absurd hodd (by decide)
  have heL : e ∉ rootGroup D b ⊔ rootGroup D a := fun heL => C.nogate e he heL h4
  have hL₁Λ : rootGroup D b ⊔ rootGroup D e ∈ rootLines D b := ⟨e, he, hbe, hbeD, heT, rfl⟩
  have hLΛ : rootGroup D b ⊔ rootGroup D a ∈ rootLines D b :=
    ⟨a, C.ha, C.hba, C.hbaD, C.haT, rfl⟩
  set N := Subgroup.normalizer (rootGroup D b : Set G) with hN
  set P := nCore D a ⊓ Subgroup.centralizer {b} with hP
  have hPN : ∀ k ∈ P, k ∈ N := by
    intro k hk
    have hkb : k * b * k⁻¹ = b := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hk.2, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h := rootGroup_conj C.isClass k b
    rw [hkb] at h
    constructor
    · intro hu
      rw [h]
      exact ⟨u, hu, rfl⟩
    · intro hu
      rw [h] at hu
      obtain ⟨v, hv, hvu⟩ := hu
      have : v = u := (MulAut.conj k).injective hvu
      rw [← this]
      exact hv
  have hPL : ∀ k ∈ P, (rootGroup D b ⊔ rootGroup D a).map (MulAut.conj k).toMonoidHom =
      rootGroup D b ⊔ rootGroup D a := by
    intro k hk
    have hkb : k * b * k⁻¹ = b := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hk.2, mul_inv_cancel_right]
    have hka : k * a * k⁻¹ = a := by
      rw [(commute_of_mem_nCore hk.1).eq, mul_inv_cancel_right]
    rw [Subgroup.map_sup, ← rootGroup_conj C.isClass, ← rootGroup_conj C.isClass, hkb, hka]
  have hP2 : IsPGroup 2 P := (isPGroup_nCore D a).to_le inf_le_left
  set ρ := hLS.lineAction C.hb with hρ
  set R : Subgroup (Equiv.Perm (rootLines D b)) := (P.subgroupOf N).map ρ with hR
  have hR2 : IsPGroup 2 R :=
    (hP2.comap_of_injective N.subtype Subtype.coe_injective).map ρ
  set L₁ : rootLines D b := ⟨_, hL₁Λ⟩ with hL₁
  set Λ' : Set (rootLines D b) := {L' | (L' : Subgroup G) ≠ rootGroup D b ⊔ rootGroup D a}
    with hΛ'
  have horbit : MulAction.orbit R L₁ = Λ' := by
    ext L'
    constructor
    · rintro ⟨σ, rfl⟩
      obtain ⟨k, hk, hkσ⟩ := σ.2
      show ((σ : Equiv.Perm (rootLines D b)) L₁ : Subgroup G) ≠ rootGroup D b ⊔ rootGroup D a
      rw [← hkσ, LineSetting.lineAction_apply]
      intro heq
      apply heL
      have h1 := congrArg (Subgroup.map (MulAut.conj ((k : N) : G)⁻¹).toMonoidHom) heq
      rw [map_conj_inv_map_conj_eq] at h1
      have h2 : (rootGroup D b ⊔ rootGroup D a).map (MulAut.conj ((k : N) : G)⁻¹).toMonoidHom =
          rootGroup D b ⊔ rootGroup D a := by
        have := hPL _ (P.inv_mem (Subgroup.mem_subgroupOf.1 hk))
        simpa using this
      rw [h2] at h1
      rw [← h1]
      exact right_mem_line he
    · intro hL'
      obtain ⟨b₂, hb₂, hbb₂, hbb₂D, hb₂T, hL'eq⟩ := L'.2
      have hb₂L : b₂ ∉ rootGroup D b ⊔ rootGroup D a :=
        hoff hb₂ hb₂T (by rw [← hL'eq]; exact hL')
      obtain ⟨⟨k, hk, hkL⟩, -⟩ := rootLinesRegularStep G D hLS b C.hb a C.ha C.hba C.hbaD C.haT
        e he hbe hbeD heL b₂ hb₂ hbb₂ hbb₂D hb₂L
      refine ⟨⟨ρ ⟨k, hPN k hk⟩, ⟨k, hPN k hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩, ?_⟩
      apply Subtype.ext
      show ((ρ ⟨k, hPN k hk⟩) L₁ : Subgroup G) = L'
      rw [LineSetting.lineAction_apply, hL'eq]
      exact hkL
  have hcard : ∃ j, Nat.card Λ' = 2 ^ j := by
    rw [← horbit]
    exact hR2.card_orbit L₁
  have hLm0 : (rootGroup D b ⊔ rootGroup D a).map (MulAut.conj h₀).toMonoidHom =
      rootGroup D b ⊔ rootGroup D a := map_conj_eq_of_forall hh₀L
  set σ₀ := ρ ⟨h₀, hh₀⟩ with hσ₀
  have hσ₀pow : σ₀ ^ orderOf h₀ = 1 := by
    rw [hσ₀, ← map_pow]
    have : (⟨h₀, hh₀⟩ : N) ^ orderOf h₀ = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  obtain ⟨j, hj⟩ := hcard
  obtain ⟨L₀, hL₀', hfix⟩ := exists_fixed_of_prime (S := Λ') (f := σ₀) (p := orderOf h₀)
    (fun L' hL' => by
      show ((σ₀ L' : rootLines D b) : Subgroup G) ≠ rootGroup D b ⊔ rootGroup D a
      rw [hσ₀, LineSetting.lineAction_apply]
      intro heq
      apply hL'
      have h1 := congrArg (Subgroup.map (MulAut.conj h₀⁻¹).toMonoidHom) heq
      rw [map_conj_inv_map_conj_eq, ← hLm0, map_conj_inv_map_conj_eq] at h1
      exact h1)
    (fun L' _ => by
      rw [← Equiv.Perm.coe_pow, hσ₀pow]
      rfl)
    (by
      rw [hj]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)))
  obtain ⟨c, hc, hbc, hbcD, hcT, hL₀eq⟩ := L₀.2
  refine ⟨c, hc, hbc, hbcD, hcT, hoff hc hcT (by rw [← hL₀eq]; exact hL₀'), fun u hu => ?_⟩
  have h1 := congrArg Subtype.val hfix
  rw [hσ₀, LineSetting.lineAction_apply, hL₀eq] at h1
  have : h₀ * u * h₀⁻¹ ∈ (rootGroup D b ⊔ rootGroup D c).map (MulAut.conj h₀).toMonoidHom :=
    ⟨u, hu, rfl⟩
  rwa [h1] at this

theorem mul_conj_mem_rootGroup {h₀ : G}
    (hpt : ∀ t ∈ D, t ∈ rootGroup D b ⊔ rootGroup D a → ∀ u ∈ rootGroup D t,
      h₀ * u * h₀⁻¹ ∈ rootGroup D t)
    (hpt' : ∀ t ∈ D, t ∈ rootGroup D b ⊔ rootGroup D a → ∀ u ∈ rootGroup D t,
      h₀⁻¹ * u * h₀ ∈ rootGroup D t)
    (hnb' : ∀ β ∈ rootGroup D b, h₀⁻¹ * β * h₀ ∈ rootGroup D b)
    (hL' : ∀ u ∈ rootGroup D b ⊔ rootGroup D a, h₀⁻¹ * u * h₀ ∈ rootGroup D b ⊔ rootGroup D a)
    {c : G} (hc : c ∈ D) (hbc : Commute b c) (hbcD : b * c ∈ D) (hcT : c ∉ rootSet D b)
    (hcL : c ∉ rootGroup D b ⊔ rootGroup D a)
    (hL₀ : ∀ u ∈ rootGroup D b ⊔ rootGroup D c, h₀ * u * h₀⁻¹ ∈ rootGroup D b ⊔ rootGroup D c) :
    c * (h₀ * c * h₀⁻¹) ∈ rootGroup D b := by
  have hD := C.root
  have hQ := C.commLambda
  have hL₀D : ∀ {u : G}, u ∈ rootGroup D b ⊔ rootGroup D c → u ≠ 1 → u ∈ D := fun hu hu1 =>
    mem_of_mem_sup_rootGroup C.hyp C.closure C.special C.hb hc hbc hbcD hcT hu hu1
  have hL₀c : ∀ {u v : G}, u ∈ rootGroup D b ⊔ rootGroup D c → v ∈ rootGroup D b ⊔ rootGroup D c →
      Commute u v := fun hu hv => commute_of_mem_sup_rootGroup C.hb hc hbc hu hv
  have hcL₀ : c ∈ rootGroup D b ⊔ rootGroup D c := right_mem_line hc
  have hbL₀ : b ∈ rootGroup D b ⊔ rootGroup D c := left_mem_line C.hb
  have hAbL₀ : rootGroup D b ≤ rootGroup D b ⊔ rootGroup D c := le_sup_left
  have htrans : ∀ {z : G}, z ∈ rootGroup D b ⊔ rootGroup D c → z ∉ rootGroup D b →
      z ∉ rootGroup D b ⊔ rootGroup D a → ∀ t ∈ rootGroup D b ⊔ rootGroup D a,
        z * t * z⁻¹ * t⁻¹ ∈ rootGroup D b := by
    intro z hz hzb hzL t ht
    have hz1 : z ≠ 1 := fun h => hzb (h ▸ (rootGroup D b).one_mem)
    have hzD := hL₀D hz hz1
    have hbz : Commute b z := hL₀c hbL₀ hz
    have hbzD : b * z ∈ D := by
      refine hL₀D (Subgroup.mul_mem _ hbL₀ hz) fun h => hzb ?_
      rw [eq_inv_of_mul_eq_one_right h, hD.inv_eq C.hb]
      exact rootSet_subset_rootGroup D b (mem_rootSet_self C.hb)
    have hza : ¬ Commute z a := fun h => hzL (C.mem_L_of_commute hzD hbz.symm h)
    have haz : orderOf (a * z) = 4 := by
      rcases commute_or_orderOf_mul_eq_four_or_odd hD C.ha hzD with h' | h4 | ⟨hodd, -⟩
      · exact absurd h'.symm hza
      · exact h4
      · exfalso
        have := Moufang.eq_of_collinear_of_odd_of_mem hD hzD C.hb hbz.symm
          (by rw [← hbz.eq]; exact hbzD) C.ha C.hba.symm hodd
        exact hzL (this ▸ C.a_mem_L)
    have ht' : t ∈ rootGroup D a ⊔ rootGroup D b := by rwa [sup_comm]
    exact mul_inv_mem_of_special hD C.closure C.special hQ C.ha C.hb C.hba.symm
      (by rw [← C.hba.eq]; exact C.hbaD) hzD hbz hbzD haz (mem_rootSet_self hzD) ht'
  have hcb : c ∉ rootGroup D b := fun h =>
    hcT (mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure C.hb h (hD.ne_one hc))
  have hc'L₀ : h₀ * c * h₀⁻¹ ∈ rootGroup D b ⊔ rootGroup D c := hL₀ c hcL₀
  have hc'b : h₀ * c * h₀⁻¹ ∉ rootGroup D b := fun h => hcb (by simpa [mul_assoc] using hnb' _ h)
  have hc'L : h₀ * c * h₀⁻¹ ∉ rootGroup D b ⊔ rootGroup D a := fun h =>
    hcL (by simpa [mul_assoc] using hL' _ h)
  have hTc := htrans hcL₀ hcb hcL
  have hTc' := htrans hc'L₀ hc'b hc'L
  have hc2 : c * c = 1 := hD.mul_self_eq_one hc
  have hci : c⁻¹ = c := hD.inv_eq hc
  have hu : ∀ t ∈ rootGroup D b ⊔ rootGroup D a, Commute (h₀ * c * h₀⁻¹ * c) t := by
    intro t ht
    refine commute_of_mul_inv_mem C.hyp C.closure C.special C.hb C.ha C.hba C.hbaD C.haT
      C.b_mem_L (hD.ne_one C.hb) C.a_mem_L (hD.ne_one C.ha) C.haT ?_ ?_ ?_ ht
    · intro s hs
      exact (hL₀c hc'L₀ (hAbL₀ hs)).mul_left (hL₀c hcL₀ (hAbL₀ hs))
    · intro t ht
      have h1 := hTc t ht
      have h2 := hTc' t ht
      have hcom : Commute (h₀ * c * h₀⁻¹) (c * t * c⁻¹ * t⁻¹) := hL₀c hc'L₀ (hAbL₀ h1)
      have e : h₀ * c * h₀⁻¹ * c * t * (h₀ * c * h₀⁻¹ * c)⁻¹ * t⁻¹ =
          (h₀ * c * h₀⁻¹ * (c * t * c⁻¹ * t⁻¹) * (h₀ * c * h₀⁻¹)⁻¹) *
            (h₀ * c * h₀⁻¹ * t * (h₀ * c * h₀⁻¹)⁻¹ * t⁻¹) := by group
      rw [e, hcom.eq, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ h1 h2
    · intro s hs
      have hcaL : c * a * c⁻¹ ∈ rootGroup D b ⊔ rootGroup D a :=
        normalizesLine_of_commute C.hyp C.closure C.special C.hb C.ha C.hba C.hbaD C.haT
          C.lineTI C.hb C.b_mem_L hc hbc.symm a C.a_mem_L
      have hcaD : c * a * c⁻¹ ∈ D := C.conj_mem c C.ha
      have h1 : c * s * c⁻¹ ∈ rootGroup D (c * a * c⁻¹) := by
        rw [rootGroup_conj C.isClass]
        exact ⟨s, hs, rfl⟩
      have h2 := hpt' _ hcaD hcaL _ h1
      have h3 : c * (h₀⁻¹ * (c * s * c⁻¹) * h₀) * c⁻¹ ∈ rootGroup D a := by
        have h4 : c * (h₀⁻¹ * (c * s * c⁻¹) * h₀) * c⁻¹ ∈
            rootGroup D (c * (c * a * c⁻¹) * c⁻¹) := by
          rw [rootGroup_conj C.isClass]
          exact ⟨_, h2, rfl⟩
        have h5 : c * (c * a * c⁻¹) * c⁻¹ = a := by
          calc c * (c * a * c⁻¹) * c⁻¹ = c * c * a * (c * c)⁻¹ := by group
            _ = a := by rw [hc2, one_mul, inv_one, mul_one]
        rwa [h5] at h4
      have h4 := hpt a C.ha C.a_mem_L _ h3
      have e : h₀ * c * h₀⁻¹ * c * s * (h₀ * c * h₀⁻¹ * c)⁻¹ =
          h₀ * (c * (h₀⁻¹ * (c * s * c⁻¹) * h₀) * c⁻¹) * h₀⁻¹ := by group
      rw [e]
      exact h4
  have huL₀ : h₀ * c * h₀⁻¹ * c ∈ rootGroup D b ⊔ rootGroup D c := Subgroup.mul_mem _ hc'L₀ hcL₀
  have huA : h₀ * c * h₀⁻¹ * c ∈ rootGroup D b := by
    by_cases hu1 : h₀ * c * h₀⁻¹ * c = 1
    · rw [hu1]
      exact (rootGroup D b).one_mem
    · have huD := hL₀D huL₀ hu1
      have huL : h₀ * c * h₀⁻¹ * c ∈ rootGroup D b ⊔ rootGroup D a :=
        C.mem_L_of_commute huD (hu b C.b_mem_L) (hu a C.a_mem_L)
      by_contra huA
      have huT : h₀ * c * h₀⁻¹ * c ∉ rootSet D b := fun h => huA (rootSet_subset_rootGroup D b h)
      have h1 := sup_rootGroup_eq_of_mem C.hyp C.closure C.special C.hb C.ha C.hba C.hbaD C.haT
        C.b_mem_L huL (hD.ne_one C.hb) hu1 huT
      have h2 := sup_rootGroup_eq_of_mem C.hyp C.closure C.special C.hb hc hbc hbcD hcT hbL₀ huL₀
        (hD.ne_one C.hb) hu1 huT
      apply hcL
      rw [← h1, h2]
      exact hcL₀
  have hcu : Commute c (h₀ * c * h₀⁻¹ * c) := hL₀c hcL₀ huL₀
  have e : c * (h₀ * c * h₀⁻¹) = h₀ * c * h₀⁻¹ * c := by
    calc c * (h₀ * c * h₀⁻¹) = c * (h₀ * c * h₀⁻¹ * c) * c⁻¹ := by group
      _ = h₀ * c * h₀⁻¹ * c := by rw [hcu.eq, mul_inv_cancel_right]
  rw [e]
  exact huA

theorem false_of_oneOpposite (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) (h1 : OneOpposite D b x) :
    False := by
  have := C.finite
  have hD := C.root
  obtain ⟨h₀, hh₀X, hp, hp2, hnb, hnb', y, hyD, hyh⟩ := C.exists_torus hl h1
  have : Fact (orderOf h₀).Prime := ⟨hp⟩
  have hbA : b ∈ rootGroup D b := rootSet_subset_rootGroup D b (mem_rootSet_self C.hb)
  have hconj1 : ∀ g : G, g * b * g⁻¹ ≠ 1 := fun g h => hD.ne_one C.hb (by
    have := congrArg (fun w => g⁻¹ * w * g) h
    simpa [mul_assoc] using this)
  have hb₀ : h₀ * b * h₀⁻¹ ∈ rootSet D b :=
    mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure C.hb (hnb b hbA) (hconj1 h₀)
  have hb₀' : h₀⁻¹ * b * h₀⁻¹⁻¹ ∈ rootSet D b := by
    rw [inv_inv]
    have := mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure C.hb (hnb' b hbA)
      (by simpa using hconj1 h₀⁻¹)
    exact this
  have hh₀X' := Subgroup.inv_mem _ hh₀X
  have hpt : ∀ t ∈ D, t ∈ rootGroup D b ⊔ rootGroup D a → ∀ u ∈ rootGroup D t,
      h₀ * u * h₀⁻¹ ∈ rootGroup D t := fun t ht htL u hu =>
    C.conj_mem_rootGroup hh₀X hb₀ ht htL hu
  have hpt' : ∀ t ∈ D, t ∈ rootGroup D b ⊔ rootGroup D a → ∀ u ∈ rootGroup D t,
      h₀⁻¹ * u * h₀ ∈ rootGroup D t := fun t ht htL u hu => by
    simpa using C.conj_mem_rootGroup hh₀X' hb₀' ht htL hu
  have hL : ∀ u ∈ rootGroup D b ⊔ rootGroup D a, h₀ * u * h₀⁻¹ ∈ rootGroup D b ⊔ rootGroup D a := by
    intro u hu
    rcases eq_or_ne u 1 with rfl | hu1
    · simp
    · exact C.conj_mem_L hh₀X (Subgroup.mem_sup_left (rootSet_subset_rootGroup D b hb₀))
        (C.mem_of_mem_L hu hu1) hu
  have hL' : ∀ u ∈ rootGroup D b ⊔ rootGroup D a,
      h₀⁻¹ * u * h₀ ∈ rootGroup D b ⊔ rootGroup D a := by
    intro u hu
    rcases eq_or_ne u 1 with rfl | hu1
    · simp
    · simpa using C.conj_mem_L hh₀X' (Subgroup.mem_sup_left (rootSet_subset_rootGroup D b hb₀'))
        (C.mem_of_mem_L hu hu1) hu
  have hh₀N : h₀ ∈ Subgroup.normalizer (rootGroup D b : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro β
    refine ⟨hnb β, fun hβ => ?_⟩
    simpa [mul_assoc] using hnb' _ hβ
  obtain ⟨c, hc, hbc, hbcD, hcT, hcL, hL₀⟩ := C.exists_fixed_line h1 hh₀N hL hp hp2
  have hcc := C.mul_conj_mem_rootGroup hpt hpt' hnb' hL' hc hbc hbcD hcT hcL hL₀
  have hc2 : c * c = 1 := hD.mul_self_eq_one hc
  set S : Set G := {w | c * w ∈ (rootGroup D b : Set G)} with hSdef
  have hScard : Nat.card S = Nat.card (rootGroup D b) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨c * w.1, w.2⟩
        invFun := fun β => ⟨c * β.1, ?_⟩
        left_inv := fun w => ?_
        right_inv := fun β => ?_ }
    · show c * (c * β.1) ∈ (rootGroup D b : Set G)
      rw [← mul_assoc, hc2, one_mul]
      exact β.2
    · apply Subtype.ext
      show c * (c * w.1) = w.1
      rw [← mul_assoc, hc2, one_mul]
    · apply Subtype.ext
      show c * (c * β.1) = β.1
      rw [← mul_assoc, hc2, one_mul]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (C.isPGroup_rootGroup b C.hb)
  obtain ⟨w, hwS, hw⟩ := exists_fixed_of_prime (S := S) (f := fun v => h₀ * v * h₀⁻¹)
    (p := orderOf h₀)
    (fun v hv => by
      show c * (h₀ * v * h₀⁻¹) ∈ rootGroup D b
      have e : c * (h₀ * v * h₀⁻¹) = c * (h₀ * c * h₀⁻¹) * (h₀ * (c * v) * h₀⁻¹) := by
        calc c * (h₀ * v * h₀⁻¹) = c * (h₀ * ((c * c) * v) * h₀⁻¹) := by rw [hc2, one_mul]
          _ = c * (h₀ * c * h₀⁻¹) * (h₀ * (c * v) * h₀⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hcc (hnb _ hv))
    (fun v _ => by
      rw [conj_iterate, pow_orderOf_eq_one, one_mul, inv_one, mul_one])
    (by
      rw [hScard, hk]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)))
  have hwL₀ : w ∈ rootGroup D b ⊔ rootGroup D c := by
    have : w = c * (c * w) := by rw [← mul_assoc, hc2, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ (right_mem_line hc) (Subgroup.mem_sup_left hwS)
  have hw1 : w ≠ 1 := by
    intro h
    apply hcT
    have hcA : c ∈ rootGroup D b := by
      have h' : c * w ∈ (rootGroup D b : Set G) := hwS
      rw [h, mul_one] at h'
      exact h'
    exact mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure C.hb hcA (hD.ne_one hc)
  have hwD : w ∈ D :=
    mem_of_mem_sup_rootGroup C.hyp C.closure C.special C.hb hc hbc hbcD hcT hwL₀ hw1
  have hcomm : Commute w h₀ := by
    have : h₀ * w = w * h₀ := by
      calc h₀ * w = h₀ * w * h₀⁻¹ * h₀ := by group
        _ = w * h₀ := by rw [hw]
    exact this.symm
  have h01 : h₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hp
    exact Nat.not_prime_one hp
  exact false_of_commute_of_inv hD C.isClass C.noPolar (hp.odd_of_ne_two hp2) h01 hwD hyD hcomm hyh

end DegenConf

end RootDegen

open RootClosure in
theorem degenerateGateStep :
    ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStructE G →
      (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D →
      Moufang.ExcCollConnected D → AllLinesTI D →
      ∀ a ∈ D, ∀ b ∈ D, ∀ x ∈ D, Commute b a → b * a ∈ D → a ∉ rootSet D b →
        ¬ Commute b x → Odd (orderOf (b * x)) → OneOpposite D b x →
        (∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a → orderOf (x * p) ≠ 4) →
        ∃ e ∈ barClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x,
          ∃ f ∈ barClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x, orderOf (e * f) = 4 := by
  intro G _ D h _ hl hc hs hconn hAll a ha b hb x hx hba hbaD haT hbx hoddbx h1 hno
  by_contra hdeg
  push Not at hdeg
  exact (RootDegen.DegenConf.mk h hc hs hconn hAll hb ha hba hbaD haT hx hbx hoddbx hno
    hdeg).false_of_oneOpposite hl h1

end CFSG.Timmesfeld.Bridge
