module

public import CFSG.Quasithin.Background.SmithB45ExcSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen

public section

namespace CFSG.Quasithin.B45Exc.HSRu

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise commutatorElement

variable {W : Type} [CommGroup W]

theorem center_eq_bot_of_cover [Finite W] (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) {S : Type} [Group S] (e : CQ L ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    Subgroup.center ↥L = ⊥ := by
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hker1 : (redHom L e).ker = ⊥ :=
    hCover ↥L (redHom L e) (redHom_surjective L e) (by rw [hker]) (by rw [hker]; exact hZodd)
  rw [← hker]
  exact hker1

@[expose] noncomputable def redEquiv {L : Subgroup (MulAut W)} {S : Type} [Group S] (e : CQ L ≃* S)
    (hcent : Subgroup.center ↥L = ⊥) : ↥L ≃* S :=
  MulEquiv.ofBijective (redHom L e) ⟨(MonoidHom.ker_eq_bot_iff _).1 (by
    have hker : (redHom L e).ker = Subgroup.center ↥L := by
      ext x
      exact redHom_eq_one_iff L e x
    rw [hker, hcent]), redHom_surjective L e⟩

structure Lift (L E : Subgroup (MulAut W)) {G : Type*} [Group G] (R P : Subgroup G) where
  hom : ↥(L ⊔ E) →* ↥R
  inj : Function.Injective hom
  mem_iff : ∀ x : ↥(L ⊔ E), ((hom x : ↥R) : G) ∈ P ↔ (x : MulAut W) ∈ L
  surj : ∀ p ∈ P, ∃ x : ↥(L ⊔ E), (x : MulAut W) ∈ L ∧ ((hom x : ↥R) : G) = p

section Build

variable [Finite W] {L E : Subgroup (MulAut W)} {S : Type} [Group S] {G : Type*} [Group G]
  {R P : Subgroup G}

noncomputable def Lift.ofAut (hW : ∀ w : W, w * w = 1) (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hEel : IsElemAbelian2 E) (e : CQ L ≃* S) (hcent : Subgroup.center ↥L = ⊥) (hPR : P ≤ R)
    (Φ : ↥R ≃* MulAut S) (θ : S ≃* ↥P)
    (hΦ : ∀ s : S, Φ ⟨(θ s : G), hPR (θ s).2⟩ = MulAut.conj s) : Lift L E R P where
  hom := Φ.symm.toMonoidHom.comp (actS hE e)
  inj := Φ.symm.injective.comp (actS_injective_of_center hW hperf hirr hE hEel e hcent)
  mem_iff := by
    have hact := actS_injective_of_center hW hperf hirr hE hEel e hcent
    have hval : ∀ l : ↥L, Φ.symm (actS hE e ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩) =
        ⟨(θ (redHom L e l) : G), hPR (θ (redHom L e l)).2⟩ := by
      intro l
      rw [actS_of_mem hE e l, MulEquiv.symm_apply_eq, hΦ]
    intro x
    constructor
    · intro hx
      set s := θ.symm ⟨_, hx⟩ with hs
      obtain ⟨l, hl⟩ := redHom_surjective L e s
      have h1 : Φ.symm (actS hE e x) = Φ.symm (actS hE e ⟨(l : MulAut W),
          Subgroup.mem_sup_left l.2⟩) := by
        rw [hval, hl, hs, MulEquiv.apply_symm_apply]
        rfl
      have h2 := hact (Φ.symm.injective h1)
      rw [h2]
      exact l.2
    · intro hx
      have := hval ⟨_, hx⟩
      show ((Φ.symm (actS hE e x) : ↥R) : G) ∈ P
      have hxe : x = ⟨((⟨_, hx⟩ : ↥L) : MulAut W), Subgroup.mem_sup_left hx⟩ := rfl
      rw [hxe, this]
      exact (θ _).2
  surj := by
    intro p hp
    obtain ⟨l, hl⟩ := redHom_surjective L e (θ.symm ⟨p, hp⟩)
    refine ⟨⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩, l.2, ?_⟩
    show ((Φ.symm (actS hE e ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩) : ↥R) : G) = p
    rw [actS_of_mem hE e l, hl]
    have : Φ.symm (MulAut.conj (θ.symm ⟨p, hp⟩)) = ⟨p, hPR hp⟩ := by
      rw [MulEquiv.symm_apply_eq, ← hΦ]
      congr 1
      apply Subtype.ext
      simp
    rw [this]

end Build

section Sylow

variable {L E : Subgroup (MulAut W)} {G : Type*} [Group G] {R P : Subgroup G}

theorem conj_mem_sup {l x : MulAut W} (hl : l ∈ L) (hx : x ∈ E) : l * x * l⁻¹ ∈ L ⊔ E :=
  (L ⊔ E).mul_mem ((L ⊔ E).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hx))
    ((L ⊔ E).inv_mem (Subgroup.mem_sup_left hl))

theorem Lift.hom_conj (ψ : Lift L E R P) (a x : ↥(L ⊔ E)) :
    ((ψ.hom (a * x * a⁻¹) : ↥R) : G) = (ψ.hom a : G) * (ψ.hom x : G) * (ψ.hom a : G)⁻¹ := by
  simp [map_mul, map_inv]

theorem Lift.exists_conj_mem [Finite G] (ψ : Lift L E R P) (hEel : IsElemAbelian2 E)
    {U : Subgroup G} (hUR : U ≤ R) (hU : Nat.card U = 2 ^ (Nat.card R).factorization 2)
    (hRUP : ∀ r ∈ R, ∃ u ∈ U, ∃ p ∈ P, r = u * p) :
    ∃ l : MulAut W, ∃ hl : l ∈ L, ∀ x (hx : x ∈ E),
      ((ψ.hom ⟨l * x * l⁻¹, conj_mem_sup hl hx⟩ : ↥R) : G) ∈ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup ↥R := (E.subgroupOf (L ⊔ E)).map ψ.hom with hB
  have hBp : IsPGroup 2 B := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : x ^ 2 = 1 := Subtype.ext (by
      have := hEel.2 _ hx
      simpa using this)
    show ψ.hom x ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, h2, map_one]
  have hU' : Nat.card (U.subgroupOf R) = 2 ^ (Nat.card R).factorization 2 := by
    rw [← hU]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv
  obtain ⟨Q, hQ⟩ := hBp.exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq ↥R Q (Sylow.ofCard (U.subgroupOf R) hU')
  obtain ⟨u, hu, p, hp, hrup⟩ := hRUP r r.2
  obtain ⟨⟨x₀, hx₀LE⟩, hx₀L, hx₀⟩ := ψ.surj p hp
  refine ⟨x₀, hx₀L, fun x hx => ?_⟩
  have hxB : ψ.hom ⟨x, Subgroup.mem_sup_right hx⟩ ∈ (Q : Subgroup ↥R) :=
    hQ ⟨⟨x, Subgroup.mem_sup_right hx⟩, hx, rfl⟩
  have hmem : MulAut.conj r • ψ.hom ⟨x, Subgroup.mem_sup_right hx⟩ ∈
      MulAut.conj r • (Q : Subgroup ↥R) :=
    Subgroup.smul_mem_pointwise_smul _ (MulAut.conj r) (Q : Subgroup ↥R) hxB
  rw [← Sylow.coe_subgroup_smul, hr, Sylow.coe_ofCard, MulAut.smul_def, MulAut.conj_apply,
    Subgroup.mem_subgroupOf] at hmem
  have hconj : ((ψ.hom ⟨x₀ * x * x₀⁻¹, conj_mem_sup hx₀L hx⟩ : ↥R) : G) =
      u⁻¹ * ((r * ψ.hom ⟨x, Subgroup.mem_sup_right hx⟩ * r⁻¹ : ↥R) : G) * u := by
    have e1 : (⟨x₀ * x * x₀⁻¹, conj_mem_sup hx₀L hx⟩ : ↥(L ⊔ E)) =
        ⟨x₀, Subgroup.mem_sup_left hx₀L⟩ * ⟨x, Subgroup.mem_sup_right hx⟩ *
          ⟨x₀, Subgroup.mem_sup_left hx₀L⟩⁻¹ := rfl
    have e2 : ψ.hom ⟨x₀, Subgroup.mem_sup_left hx₀L⟩ = ⟨p, by
        rw [← hx₀]; exact (ψ.hom _).2⟩ := Subtype.ext hx₀
    rw [e1, Lift.hom_conj, e2]
    have hpr : p = u⁻¹ * (r : G) := by rw [hrup]; group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hpr]
    group
  rw [hconj]
  exact U.mul_mem (U.mul_mem (U.inv_mem hu) hmem) hu

end Sylow

section Dihedral

variable {L E : Subgroup (MulAut W)} {G : Type*} [Group G] {R P : Subgroup G}

theorem Lift.exists_dihedral (ψ : Lift L E R P) (b : ↥(L ⊔ E)) {g : G} (hg : g ∈ P) :
    ∃ h : ↥(L ⊔ E), (h : MulAut W) ∈ L ∧
      ((ψ.hom (b * (h * b * h⁻¹)) : ↥R) : G) = (ψ.hom b : G) * (g * (ψ.hom b : G) * g⁻¹) := by
  obtain ⟨h, hL, hh⟩ := ψ.surj g hg
  refine ⟨h, hL, ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hh]

theorem Lift.mem_of_mem (ψ : Lift L E R P) {x : ↥(L ⊔ E)} (hx : ((ψ.hom x : ↥R) : G) ∈ P) :
    (x : MulAut W) ∈ L :=
  (ψ.mem_iff x).1 hx

theorem Lift.eq_of_hom_eq (ψ : Lift L E R P) {x y : ↥(L ⊔ E)}
    (h : ((ψ.hom x : ↥R) : G) = ((ψ.hom y : ↥R) : G)) : x = y :=
  ψ.inj (Subtype.ext h)

theorem index_fixV_dihedral_le [Finite W] (b h : MulAut W) :
    (fixV (Subgroup.zpowers (b * (h * b * h⁻¹)))).index ≤
      (fixV (Subgroup.zpowers b)).index ^ 2 := by
  rw [sq]
  calc (fixV (Subgroup.zpowers (b * (h * b * h⁻¹)))).index
      ≤ (fixV (Subgroup.zpowers b)).index * (fixV (Subgroup.zpowers (h * b * h⁻¹))).index :=
        index_fixV_mul_le b _
    _ = (fixV (Subgroup.zpowers b)).index * (fixV (Subgroup.zpowers b)).index := by
        rw [index_fixV_conj]

end Dihedral

section Pull

variable [Finite W] {L E : Subgroup (MulAut W)} {G : Type*} [Group G] {R P : Subgroup G}

omit [Finite W] in
theorem Lift.exists_dihedral_conj (ψ : Lift L E R P) (b : ↥(L ⊔ E)) {g t G₀ : G} (hg : g ∈ P)
    (hG₀ : G₀ ∈ P) (hb : ((ψ.hom b : ↥R) : G) = g * t * g⁻¹) :
    ∃ h : ↥(L ⊔ E), (h : MulAut W) ∈ L ∧
      ((ψ.hom (b * (h * b * h⁻¹)) : ↥R) : G) = g * (t * (G₀ * t * G₀⁻¹)) * g⁻¹ := by
  obtain ⟨h, hL, hh⟩ := ψ.exists_dihedral b (P.mul_mem (P.mul_mem hg hG₀) (P.inv_mem hg))
  refine ⟨h, hL, ?_⟩
  rw [hh, hb]
  group

theorem Lift.exists_mem_dihedral (ψ : Lift L E R P) (b : ↥(L ⊔ E)) {g t G₀ : G} (hg : g ∈ P)
    (hG₀ : G₀ ∈ P) (hb : ((ψ.hom b : ↥R) : G) = g * t * g⁻¹) (hy₀ : t * (G₀ * t * G₀⁻¹) ∈ P) :
    ∃ z : MulAut W, z ∈ L ∧
      (fixV (Subgroup.zpowers z)).index ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index ^ 2 ∧
      ∀ n : ℕ, z ^ n = 1 ↔ (t * (G₀ * t * G₀⁻¹)) ^ n = 1 := by
  obtain ⟨h, -, hh⟩ := ψ.exists_dihedral_conj b hg hG₀ hb
  set y : ↥(L ⊔ E) := b * (h * b * h⁻¹) with hy
  have hyP : ((ψ.hom y : ↥R) : G) ∈ P := by
    rw [hh]
    exact P.mul_mem (P.mul_mem hg hy₀) (P.inv_mem hg)
  refine ⟨y, ψ.mem_of_mem hyP, ?_, fun n => ?_⟩
  · have e : ((y : ↥(L ⊔ E)) : MulAut W) =
        (b : MulAut W) * ((h : MulAut W) * b * (h : MulAut W)⁻¹) := by
      simp [hy]
    rw [e]
    exact index_fixV_dihedral_le _ _
  · have e1 : ((y : MulAut W)) ^ n = ((y ^ n : ↥(L ⊔ E)) : MulAut W) := by simp
    have e2 : ((ψ.hom (y ^ n) : ↥R) : G) = g * (t * (G₀ * t * G₀⁻¹)) ^ n * g⁻¹ := by
      rw [map_pow, SubgroupClass.coe_pow, hh, conj_pow]
    constructor
    · intro hn
      have h1 : y ^ n = 1 := Subtype.ext (by rw [← e1, hn]; rfl)
      have h2 := congrArg (fun x : ↥(L ⊔ E) => ((ψ.hom x : ↥R) : G)) h1
      simp only [e2, map_one, OneMemClass.coe_one] at h2
      calc (t * (G₀ * t * G₀⁻¹)) ^ n
          = g⁻¹ * (g * (t * (G₀ * t * G₀⁻¹)) ^ n * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    · intro hn
      have h1 : y ^ n = 1 := ψ.eq_of_hom_eq (by rw [e2, hn, map_one]; simp)
      rw [e1, h1]
      rfl

theorem Lift.two_pow_le_sq_of_cfg (hW : ∀ w : W, w * w = 1) (ψ : Lift L E R P) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (b : ↥(L ⊔ E)) {g t G₁ X Y : G} (hg : g ∈ P)
    (hG₁ : G₁ ∈ P) (hX : X ∈ P) (hY : Y ∈ P) (hb : ((ψ.hom b : ↥R) : G) = g * t * g⁻¹)
    (hZ : t * (G₁ * t * G₁⁻¹) = ⁅X, Y⁆) (hXp : X ^ p = 1) (hzx : Commute ⁅X, Y⁆ X)
    (hzy : Commute ⁅X, Y⁆ Y) (hz1 : ⁅X, Y⁆ ≠ 1) :
    2 ^ (p * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index ^ 2 := by
  obtain ⟨h, -, hh⟩ := ψ.exists_dihedral_conj b hg hG₁ hb
  obtain ⟨x, -, hx⟩ := ψ.surj (g * X * g⁻¹) (P.mul_mem (P.mul_mem hg hX) (P.inv_mem hg))
  obtain ⟨y, -, hy⟩ := ψ.surj (g * Y * g⁻¹) (P.mul_mem (P.mul_mem hg hY) (P.inv_mem hg))
  have hcomm : ((ψ.hom ⁅x, y⁆ : ↥R) : G) = g * ⁅X, Y⁆ * g⁻¹ := by
    rw [map_commutatorElement, commutatorElement_def, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx, hy]
    group
  have hyz : b * (h * b * h⁻¹) = ⁅x, y⁆ := ψ.eq_of_hom_eq (by rw [hh, hcomm, hZ])
  have hxp : x ^ p = 1 := ψ.eq_of_hom_eq (by
    rw [map_pow, SubgroupClass.coe_pow, hx, conj_pow, hXp, map_one]
    simp)
  have hzx' : x * ⁅x, y⁆ = ⁅x, y⁆ * x := ψ.eq_of_hom_eq (by
    simp only [map_mul, Subgroup.coe_mul, hcomm, hx]
    rw [show g * X * g⁻¹ * (g * ⁅X, Y⁆ * g⁻¹) = g * (X * ⁅X, Y⁆) * g⁻¹ by group,
      show g * ⁅X, Y⁆ * g⁻¹ * (g * X * g⁻¹) = g * (⁅X, Y⁆ * X) * g⁻¹ by group, hzx.eq])
  have hzy' : y * ⁅x, y⁆ = ⁅x, y⁆ * y := ψ.eq_of_hom_eq (by
    simp only [map_mul, Subgroup.coe_mul, hcomm, hy]
    rw [show g * Y * g⁻¹ * (g * ⁅X, Y⁆ * g⁻¹) = g * (Y * ⁅X, Y⁆) * g⁻¹ by group,
      show g * ⁅X, Y⁆ * g⁻¹ * (g * Y * g⁻¹) = g * (⁅X, Y⁆ * Y) * g⁻¹ by group, hzy.eq])
  have hz1' : ⁅x, y⁆ ≠ 1 := by
    intro h1
    apply hz1
    have := congrArg (fun u : ↥(L ⊔ E) => ((ψ.hom u : ↥R) : G)) h1
    simp only [hcomm, map_one, OneMemClass.coe_one] at this
    calc ⁅X, Y⁆ = g⁻¹ * (g * ⁅X, Y⁆ * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  have hzxc : Commute ⁅x, y⁆ x := hzx'.symm
  have hzyc : Commute ⁅x, y⁆ y := hzy'.symm
  have hzp : ⁅x, y⁆ ^ p = 1 := heis_comm_pow hzxc hzyc hxp
  have hcfg := extraCfg_map (L ⊔ E).subtype (Subgroup.subtype_injective _) hxp hzp hzx' hzy'
    (heis_yinv_x_y hzxc hzyc) hz1'
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 := two_pow_le_index_center_of_cfg hcfg hW hodd
  have e : (((L ⊔ E).subtype ⁅x, y⁆ : MulAut W)) =
      (b : MulAut W) * ((h : MulAut W) * b * (h : MulAut W)⁻¹) := by
    rw [← hyz]
    simp
  rw [e] at h1
  exact h1.trans (index_fixV_dihedral_le _ _)

end Pull

section Gen

variable {L E : Subgroup (MulAut W)} {G : Type*} [Group G] {R P : Subgroup G}

@[expose] def Lift.toG (ψ : Lift L E R P) : ↥(L ⊔ E) →* G := R.subtype.comp ψ.hom

theorem Lift.toG_apply (ψ : Lift L E R P) (x : ↥(L ⊔ E)) :
    ψ.toG x = ((ψ.hom x : ↥R) : G) := rfl

theorem Lift.toG_injective (ψ : Lift L E R P) : Function.Injective ψ.toG :=
  (Subgroup.subtype_injective R).comp ψ.inj

theorem Lift.le_sup_of_le_closure (ψ : Lift L E R P) {F : Subgroup (MulAut W)} {g : G}
    (hg : g ∈ P)
    (hgen : P ≤ Subgroup.closure (((F.subgroupOf (L ⊔ E)).map ψ.toG : Set G) ∪
      (fun y => g * y * g⁻¹) '' ((F.subgroupOf (L ⊔ E)).map ψ.toG : Set G))) :
    ∃ h : MulAut W, h ∈ L ∧ L ≤ F ⊔ F.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨h, hhL, hh⟩ := ψ.surj g hg
  refine ⟨h, hhL, fun y hy => ?_⟩
  set F' : Subgroup ↥(L ⊔ E) := F.subgroupOf (L ⊔ E) with hF'
  set X : Subgroup ↥(L ⊔ E) :=
    Subgroup.closure ((F' : Set ↥(L ⊔ E)) ∪ (fun x => h * x * h⁻¹) '' (F' : Set ↥(L ⊔ E)))
    with hX
  have hXmap : X.map ψ.toG = Subgroup.closure ((F'.map ψ.toG : Set G) ∪
      (fun y => g * y * g⁻¹) '' (F'.map ψ.toG : Set G)) := by
    rw [hX, MonoidHom.map_closure, Set.image_union, Subgroup.coe_map]
    congr 2
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    rw [map_mul, map_mul, map_inv, Lift.toG_apply ψ h, hh]
  set y' : ↥(L ⊔ E) := ⟨y, Subgroup.mem_sup_left hy⟩ with hy'
  have hyP : ψ.toG y' ∈ P := (ψ.mem_iff y').2 hy
  have hyX : ψ.toG y' ∈ X.map ψ.toG := by
    rw [hXmap]
    exact hgen hyP
  obtain ⟨x, hxX, hxy⟩ := hyX
  have hxy' : x = y' := ψ.toG_injective hxy
  rw [hxy'] at hxX
  have hXle : X.map (L ⊔ E).subtype ≤ F ⊔ F.map (MulAut.conj (h : MulAut W)).toMonoidHom := by
    rw [hX, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨z, hz | ⟨u, hu, rfl⟩, rfl⟩
    · exact Subgroup.mem_sup_left hz
    · refine Subgroup.mem_sup_right ⟨(u : MulAut W), hu, ?_⟩
      simp
  exact hXle ⟨y', hxX, rfl⟩

end Gen

end CFSG.Quasithin.B45Exc.HSRu
