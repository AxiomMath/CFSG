module

public import CFSG.RankThree.GF2n.Smith81.Sec1Types
public import CFSG.RankThree.GF2n.Stroth80.Sec26
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Kx (Q X : Subgroup G) : Subgroup G := Q ⊓ Subgroup.normalizer (X : Set G)

@[expose] def Lx (M X : Subgroup G) : Subgroup G := QB X ⊓ M

@[expose] def Jx (Q X : Subgroup G) (x : G) : Subgroup G := ⁅Q, Subgroup.zpowers x⁆ ⊓ QB X

structure Sit (M Q Z X : Subgroup G) (x : G) : Prop where
  hyp : StrothHyp M Q Z
  conj : ∃ g : G, X = conjSubgroup g Z
  mem : x ∈ X
  ne_one : x ≠ 1
  memM : x ∈ M
  notQ : x ∉ Q

theorem Sit.of_conj {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {g z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (hM : g * z * g⁻¹ ∈ M) (hQ : g * z * g⁻¹ ∉ Q) :
    Sit M Q Z (conjSubgroup g Z) (g * z * g⁻¹) :=
  ⟨H, ⟨g, rfl⟩,
    mem_conjSubgroup.mpr (by rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]; exact hz),
    fun h => hz1 (by
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h]; group), hM, hQ⟩

@[expose] def Post12 (M Q Z X : Subgroup G) : Prop := X ≤ H0 M Z ∧ X ⊓ Q = ⊥

section Conj

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

private theorem normalizer_conj_aux (g : G) (T : Subgroup G) :
    Subgroup.normalizer (conjSubgroup g T : Set G) =
      conjSubgroup g (Subgroup.normalizer (T : Set G)) :=
  (Subgroup.map_normalizer_eq_of_bijective (f := (MulAut.conj g).toMonoidHom) T
    (MulAut.conj g).bijective).symm

private theorem inSubgroup_gF_conj (N : Subgroup G) (g : G) :
    inSubgroup generalizedFitting (conjSubgroup g N) =
      conjSubgroup g (inSubgroup generalizedFitting N) := by
  let e : ↥N ≃* ↥(conjSubgroup g N) := MulEquiv.subgroupMap (MulAut.conj g) N
  have key := CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  show (generalizedFitting ↥(conjSubgroup g N)).map (conjSubgroup g N).subtype =
    ((generalizedFitting ↥N).map N.subtype).map (MulAut.conj g).toMonoidHom
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1 <;> ext x <;> rfl

theorem normalizer_conj_eq (H : StrothHyp M Q Z) (g : G) :
    Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) = conjSubgroup g M := by
  rw [normalizer_conj_aux, H.normalizer_Z.1]

theorem QB_conj_eq (H : StrothHyp M Q Z) (g : G) :
    QB (conjSubgroup g Z) = conjSubgroup g Q := by
  unfold QB
  rw [normalizer_conj_eq H g, inSubgroup_gF_conj]
  congr 1
  rw [H.hQ]
  unfold inSubgroup
  rw [H.fitting]

theorem conjSubgroup_eq_of_mem_ne_one (H : StrothHyp M Q Z) {g g' y : G} (hy1 : y ≠ 1)
    (hy : y ∈ conjSubgroup g Z) (hy' : y ∈ conjSubgroup g' Z) :
    conjSubgroup g Z = conjSubgroup g' Z := by
  have h1 : g⁻¹ * y * g ∈ Z := mem_conjSubgroup.mp hy
  have h2 : g⁻¹ * y * g ∈ conjSubgroup (g⁻¹ * g') Z := by
    rw [mem_conjSubgroup]
    have : (g⁻¹ * g')⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * g') = g'⁻¹ * y * g' := by group
    rw [this]
    exact mem_conjSubgroup.mp hy'
  have hne : Z ⊓ conjSubgroup (g⁻¹ * g') Z ≠ ⊥ := by
    intro hbot
    have : g⁻¹ * y * g ∈ Z ⊓ conjSubgroup (g⁻¹ * g') Z := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot] at this
    apply hy1
    have h3 : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [h3, this]; group
  have h4 := conjSubgroup_eq_of_isTI H.ti hne
  calc conjSubgroup g Z = conjSubgroup g (conjSubgroup (g⁻¹ * g') Z) := by rw [h4]
    _ = conjSubgroup (g * (g⁻¹ * g')) Z := (conjSubgroup_mul g _ Z).symm
    _ = conjSubgroup g' Z := by rw [mul_inv_cancel_left]

end Conj

section Facts

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem Sit.X_ne_Z (hs : Sit M Q Z X x) : X ≠ Z := by
  intro h
  exact hs.notQ (hs.hyp.Z_normal.1 (h ▸ hs.mem))

theorem Sit.Z_inf_X (hs : Sit M Q Z X x) : Z ⊓ X = ⊥ := by
  obtain ⟨g, hg⟩ := hs.conj
  rw [hg]
  exact inf_conjSubgroup_eq_bot_of_isTI hs.hyp.ti (hg ▸ hs.X_ne_Z)

theorem Sit.X_isTI (hs : Sit M Q Z X x) : IsTI X := by
  obtain ⟨g, hg⟩ := hs.conj
  rw [hg]
  exact isTI_conjSubgroup hs.hyp.ti g

theorem Sit.QB_eq (hs : Sit M Q Z X x) : ∃ g : G, X = conjSubgroup g Z ∧
    QB X = conjSubgroup g Q ∧ Subgroup.normalizer (X : Set G) = conjSubgroup g M := by
  obtain ⟨g, hg⟩ := hs.conj
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hg]; exact QB_conj_eq hs.hyp g
  · rw [hg]; exact normalizer_conj_eq hs.hyp g

theorem Sit.X_sq (hs : Sit M Q Z X x) : ∀ y ∈ X, y * y = 1 := by
  obtain ⟨g, hg⟩ := hs.conj
  intro y hy
  rw [hg, mem_conjSubgroup] at hy
  have h1 := Z_sq hs.hyp hy
  have e : y * y = g * ((g⁻¹ * y * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
  rw [e, h1]; group

theorem Sit.X_comm (hs : Sit M Q Z X x) : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  obtain ⟨g, hg⟩ := hs.conj
  intro a ha b hb
  rw [hg, mem_conjSubgroup] at ha hb
  have h1 := Z_central hs.hyp ha (hs.hyp.Z_normal.1 hb)
  have e1 : a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
  have e2 : b * a = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
  rw [e1, e2, h1]

theorem Sit.normalizer_QB (hs : Sit M Q Z X x) {k : G} (hk : k ∈ Subgroup.normalizer (X : Set G))
    {y : G} (hy : y ∈ QB X) : k * y * k⁻¹ ∈ QB X := by
  obtain ⟨g, -, hQB, hN⟩ := hs.QB_eq
  rw [hN, mem_conjSubgroup] at hk
  rw [hQB, mem_conjSubgroup] at hy ⊢
  have h1 := (Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hk) _).mp hy
  have : g⁻¹ * k * g * (g⁻¹ * y * g) * (g⁻¹ * k * g)⁻¹ = g⁻¹ * (k * y * k⁻¹) * g := by group
  rwa [this] at h1

theorem Sit.QB_le_normalizer (hs : Sit M Q Z X x) : QB X ≤ Subgroup.normalizer (X : Set G) := by
  unfold QB
  exact Subgroup.map_subtype_le _

theorem Sit.QB_comm_X (hs : Sit M Q Z X x) {u y : G} (hu : u ∈ X) (hy : y ∈ QB X) :
    u * y = y * u := by
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  rw [hg] at hu
  rw [hQB] at hy
  exact hs.hyp.toHyp79.conj_central g hu hy

theorem Sit.comm_QB_mem_X (hs : Sit M Q Z X x) {a b : G} (ha : a ∈ QB X) (hb : b ∈ QB X) :
    ⁅a, b⁆ ∈ X := by
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  rw [hQB] at ha hb
  rw [hg]
  exact hs.hyp.toHyp79.comm_mem_conj g ha hb

theorem Z_inf_QB_eq_bot (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) :
    Z ⊓ QB X = ⊥ := by
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  rw [eq_bot_iff]
  intro z₁ hz₁
  obtain ⟨hz₁Z, hz₁Q⟩ := Subgroup.mem_inf.mp hz₁
  by_contra hz1
  have hz1' : z₁ ≠ 1 := fun h => hz1 (by rw [h]; exact Subgroup.one_mem _)
  rw [hQB, mem_conjSubgroup] at hz₁Q
  set u := g⁻¹ * z₁ * g with hu
  have hu1 : u ≠ 1 := by
    intro h
    apply hz1'
    have : z₁ = g * u * g⁻¹ := by rw [hu]; group
    rw [this, h]; group
  have huB : u ∈ conjSubgroup g⁻¹ Z := by
    rw [mem_conjSubgroup]
    simpa [hu, mul_assoc] using hz₁Z
  have huZ : u ∉ Z := by
    intro huZ
    have h1 : conjSubgroup g⁻¹ Z = Z := by
      have := conjSubgroup_eq_of_mem_ne_one hs.hyp (g := 1) (g' := g⁻¹) hu1
        (by rwa [conjSubgroup_one]) huB
      rw [conjSubgroup_one] at this
      exact this.symm
    apply hs.X_ne_Z
    rw [hg]
    calc conjSubgroup g Z = conjSubgroup g (conjSubgroup g⁻¹ Z) := by rw [h1]
      _ = Z := by rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  obtain ⟨g', hg'Q, hug'⟩ := stroth_2_6 hs.hyp hz₁Q huZ ⟨g⁻¹, z₁, hz₁Z, by rw [hu]; group⟩
  have hB : conjSubgroup g⁻¹ Z = conjSubgroup g' Z :=
    conjSubgroup_eq_of_mem_ne_one hs.hyp hu1 huB hug'
  have hBQ : conjSubgroup g⁻¹ Z ≤ Q := hB ▸ hg'Q
  have hBne : conjSubgroup g⁻¹ Z ≠ Z := by
    intro h1
    apply hs.X_ne_Z
    rw [hg]
    calc conjSubgroup g Z = conjSubgroup g (conjSubgroup g⁻¹ Z) := by rw [h1]
      _ = Z := by rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have hc : Ctx M Q Z (conjSubgroup g⁻¹ Z) := ⟨hs.hyp, ⟨g⁻¹, rfl⟩, hBQ, hBne⟩
  have hZle := (Ctx.Z_le_QB hc).1
  rw [(Ctx.QB_eq hc (g := g⁻¹) rfl).2] at hZle
  have hXQ : X ≤ Q := by
    intro y hy
    rw [hg, mem_conjSubgroup] at hy
    have := hZle hy
    rw [mem_conjSubgroup] at this
    have e : (g⁻¹)⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  have : x ∈ X ⊓ Q := ⟨hs.mem, hXQ hs.mem⟩
  rw [h12.2, Subgroup.mem_bot] at this
  exact hs.ne_one this

end Facts

section Smith113

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem Z_le_normalizer_X (h12 : Post12 M Q Z X) : Z ≤ Subgroup.normalizer (X : Set G) :=
  le_normalizer_of_comm fun z hz w hw => Subgroup.mem_centralizer_iff.mp (h12.1 hw).2 z hz

theorem Lx_le_H0 (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) :
    Lx M X ≤ H0 M Z := by
  intro l hl
  obtain ⟨hlQ, hlM⟩ := Subgroup.mem_inf.mp hl
  refine ⟨hlM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have h1 : ⁅l, z⁆ ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (hs.hyp.Z_normal.2 hlM) z).mp hz
    rw [commutatorElement_def]
    exact Z.mul_mem this (Z.inv_mem hz)
  have h2 : ⁅l, z⁆ ∈ QB X := by
    have hzl : z * l⁻¹ * z⁻¹ ∈ QB X :=
      hs.normalizer_QB (Z_le_normalizer_X h12 hz) ((QB X).inv_mem hlQ)
    have e : ⁅l, z⁆ = l * (z * l⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (QB X).mul_mem hlQ hzl
  have h3 : ⁅l, z⁆ ∈ Z ⊓ QB X := ⟨h1, h2⟩
  rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

theorem Kx_le_centralizer_X (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) :
    Kx Q X ≤ Subgroup.centralizer (X : Set G) := by
  intro k hk
  obtain ⟨hkQ, hkN⟩ := Subgroup.mem_inf.mp hk
  refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  have h1 : ⁅k, w⁆ ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp hkN w).mp hw
    rw [commutatorElement_def]
    exact X.mul_mem this (X.inv_mem hw)
  have h2 : ⁅k, w⁆ ∈ Q := by
    have hwM : w ∈ M := (h12.1 hw).1
    have e : ⁅k, w⁆ = k * (w * k⁻¹ * w⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem hkQ (conj_mem_Q hs.hyp hwM (Q.inv_mem hkQ))
  have h3 : ⁅k, w⁆ ∈ X ⊓ Q := ⟨h1, h2⟩
  rw [h12.2, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

theorem Kx_eq (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) :
    Kx Q X = Q ⊓ Subgroup.centralizer ({x} : Set G) := by
  apply le_antisymm
  · intro k hk
    exact ⟨hk.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs.mem)
      (Kx_le_centralizer_X hs h12 hk)⟩
  · intro y hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    have hcomm : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    exact ⟨hyQ, Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hs.mem hs.ne_one hcomm⟩

theorem Kx_inf_Lx (hs : Sit M Q Z X x) : Kx Q X ⊓ Lx M X = Q ⊓ QB X := by
  apply le_antisymm
  · intro y hy
    exact ⟨hy.1.1, hy.2.1⟩
  · intro y hy
    exact ⟨⟨hy.1, hs.QB_le_normalizer hy.2⟩, ⟨hy.2, hs.hyp.Q_normal.1 hy.1⟩⟩

theorem smith_1_13_of_post12 (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) :
    ⁅Kx Q X, Lx M X⁆ ≤ Q ⊓ QB X ∧
    Kx Q X ≤ Subgroup.centralizer ((Q ⊓ QB X : Subgroup G) : Set G) ∧
    Lx M X ≤ Subgroup.centralizer ((Q ⊓ QB X : Subgroup G) : Set G) ∧
    Q ⊓ QB X ≤ Q ⊓ Subgroup.centralizer ({x} : Set G) ∧
    ∀ d ∈ Q ⊓ QB X, ∀ y ∈ Q ⊓ Subgroup.centralizer ({x} : Set G), d * y = y * d := by
  have hZQ := hs.hyp.Z_normal.1
  have hK : Kx Q X ≤ Subgroup.centralizer ((Q ⊓ QB X : Subgroup G) : Set G) := by
    intro k hk
    obtain ⟨hkQ, hkN⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
    obtain ⟨hdQ, hdB⟩ := Subgroup.mem_inf.mp hd
    have h1 : ⁅k, d⁆ ∈ Z := comm_mem_Z hs.hyp hkQ hdQ
    have h2 : ⁅k, d⁆ ∈ QB X := by
      have hkd : k * d * k⁻¹ ∈ QB X := hs.normalizer_QB hkN hdB
      rw [commutatorElement_def]
      exact (QB X).mul_mem hkd ((QB X).inv_mem hdB)
    have h3 : ⁅k, d⁆ ∈ Z ⊓ QB X := ⟨h1, h2⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  refine ⟨?_, hK, ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro k hk l hl
    obtain ⟨hkQ, hkN⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨hlB, hlM⟩ := Subgroup.mem_inf.mp hl
    refine ⟨?_, ?_⟩
    · have e : ⁅k, l⁆ = k * (l * k⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Q.mul_mem hkQ (conj_mem_Q hs.hyp hlM (Q.inv_mem hkQ))
    · have hkl : k * l * k⁻¹ ∈ QB X := hs.normalizer_QB hkN hlB
      rw [commutatorElement_def]
      exact (QB X).mul_mem hkl ((QB X).inv_mem hlB)
  · intro l hl
    obtain ⟨hlB, hlM⟩ := Subgroup.mem_inf.mp hl
    refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
    obtain ⟨hdQ, hdB⟩ := Subgroup.mem_inf.mp hd
    have h1 : ⁅l, d⁆ ∈ X := hs.comm_QB_mem_X hlB hdB
    have h2 : ⁅l, d⁆ ∈ Q := by
      have e : ⁅l, d⁆ = (l * d * l⁻¹) * d⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact Q.mul_mem (conj_mem_Q hs.hyp hlM hdQ) (Q.inv_mem hdQ)
    have h3 : ⁅l, d⁆ ∈ X ⊓ Q := ⟨h1, h2⟩
    rw [h12.2, Subgroup.mem_bot] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  · intro d hd
    exact ⟨hd.1, Subgroup.mem_centralizer_singleton_iff.mpr (hs.QB_comm_X hs.mem hd.2).symm⟩
  · intro d hd y hy
    have hyK : y ∈ Kx Q X := by rw [Kx_eq hs h12]; exact hy
    exact Subgroup.mem_centralizer_iff.mp (hK hyK) d hd

end Smith113

section Smith116

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem Sit.x_sq (hs : Sit M Q Z X x) : x * x = 1 := by
  obtain ⟨g, hg⟩ := hs.conj
  have hx := hs.mem
  rw [hg, mem_conjSubgroup] at hx
  have h1 := Z_sq hs.hyp hx
  have e : x * x = g * ((g⁻¹ * x * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
  rw [e, h1]; group

theorem Sit.x_cent (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) : ∀ z ∈ Z, x * z * x⁻¹ = z := by
  intro z hz
  have := Subgroup.mem_centralizer_iff.mp (h12.1 hs.mem).2 z hz
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem smith_1_16_of_post12 (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) {b : G}
    (hb : b ∈ Jx Q X x) (hb1 : b ≠ 1) : ∃ (g z : G), z ∈ Z ∧ b = g * (x * z) * g⁻¹ := by
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hZQ := hs.hyp.Z_normal.1
  obtain ⟨hbD, hbB⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨K, _, _, γ, M₀, hD, hcard, hK2, ⟨A⟩⟩ := exists_model hs.hyp hs.memM hxZ
  have hbQ : b ∈ Q := by
    rw [commutator_zpowers_eq_closure' hx2] at hbD
    exact D_le_Q hs.hyp hs.memM hbD
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  have hb' : g⁻¹ * b * g ∈ Q := by
    have := hbB; rw [hQB, mem_conjSubgroup] at this; exact this
  have hb'Z : g⁻¹ * b * g ∉ Z := by
    intro hZ
    have hbXg : b ∈ X := by rw [hg, mem_conjSubgroup]; exact hZ
    have : b ∈ X ⊓ Q := ⟨hbXg, hbQ⟩
    rw [h12.2, Subgroup.mem_bot] at this
    exact hb1 this
  have hz' : g⁻¹ * x * g ∈ Z := by
    have := hs.mem; rw [hg, mem_conjSubgroup] at this; exact this
  obtain ⟨q', hq', hq'c⟩ := GM.exists_comm hD hb' hb'Z hz'
  set u := g * q' * g⁻¹ with hu
  have hbu : ⁅b, u⁆ = x := by
    have : ⁅b, u⁆ = g * ⁅g⁻¹ * b * g, q'⁆ * g⁻¹ := by
      simp only [hu, commutatorElement_def]; group
    rw [this, hq'c]; group
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hub : u * b * u⁻¹ = x * b := by
    have : u * b * u⁻¹ = ⁅b, u⁆⁻¹ * b := by simp only [commutatorElement_def]; group
    rw [this, hbu, hxinv]
  have hπb : M₀.π b ∈ commSpace A :=
    ((mem_commSup_iff A hs.hyp hs.memM hx2 hZQ).mp (Subgroup.mem_sup_left hbD)).2
  obtain ⟨q, hq, z₀, hz₀, hbq⟩ := exists_comm_rep A hs.hyp hs.memM hbQ hπb
  have hb2 : b ^ 2 ∈ Z := sq_mem_Z hs.hyp hbQ
  have hqb : ⁅q, b⁆ ∈ Z := comm_mem_Z hs.hyp hq hbQ
  have hwZ : b ^ 2 * z₀⁻¹ * ⁅q, b⁆ ∈ Z := Z.mul_mem (Z.mul_mem hb2 (Z.inv_mem hz₀)) hqb
  have hxb : x * b = b * x := hs.QB_comm_X hs.mem hbB
  have hxz : x * z₀⁻¹ = z₀⁻¹ * x := mul_inv_eq_iff_eq_mul.mp (hxZ _ (Z.inv_mem hz₀))
  have hac : (z₀⁻¹ * ⁅q, b⁆) * b = b * (z₀⁻¹ * ⁅q, b⁆) :=
    Z_central hs.hyp (Z.mul_mem (Z.inv_mem hz₀) hqb) hbQ
  have key : q * (x * b) * q⁻¹ = x * (b ^ 2 * z₀⁻¹ * ⁅q, b⁆) := by
    have e1 : q * (x * b) * q⁻¹ = (q * x * q⁻¹) * (q * b * q⁻¹) := by group
    have e2 : q * x * q⁻¹ = ⁅q, x⁆ * x := by simp only [commutatorElement_def]; group
    have e3 : q * b * q⁻¹ = ⁅q, b⁆ * b := by simp only [commutatorElement_def]; group
    have e4 : ⁅q, x⁆ = b * z₀⁻¹ := by rw [hbq]; group
    rw [e1, e2, e3, e4]
    calc b * z₀⁻¹ * x * (⁅q, b⁆ * b)
        = b * (z₀⁻¹ * x) * (⁅q, b⁆ * b) := by simp only [mul_assoc]
      _ = b * (x * z₀⁻¹) * (⁅q, b⁆ * b) := by rw [← hxz]
      _ = (b * x) * z₀⁻¹ * (⁅q, b⁆ * b) := by simp only [mul_assoc]
      _ = (x * b) * z₀⁻¹ * (⁅q, b⁆ * b) := by rw [← hxb]
      _ = x * (b * ((z₀⁻¹ * ⁅q, b⁆) * b)) := by simp only [mul_assoc]
      _ = x * (b * (b * (z₀⁻¹ * ⁅q, b⁆))) := by rw [hac]
      _ = x * (b ^ 2 * z₀⁻¹ * ⁅q, b⁆) := by rw [sq]; simp only [mul_assoc]
  refine ⟨(q * u)⁻¹, b ^ 2 * z₀⁻¹ * ⁅q, b⁆, hwZ, ?_⟩
  have h1 : (q * u) * b * (q * u)⁻¹ = x * (b ^ 2 * z₀⁻¹ * ⁅q, b⁆) := by
    calc (q * u) * b * (q * u)⁻¹ = q * (u * b * u⁻¹) * q⁻¹ := by group
      _ = q * (x * b) * q⁻¹ := by rw [hub]
      _ = x * (b ^ 2 * z₀⁻¹ * ⁅q, b⁆) := key
  calc b = (q * u)⁻¹ * ((q * u) * b * (q * u)⁻¹) * (q * u) := by group
    _ = (q * u)⁻¹ * (x * (b ^ 2 * z₀⁻¹ * ⁅q, b⁆)) * ((q * u)⁻¹)⁻¹ := by rw [h1, inv_inv]

end Smith116

end CFSG.RankThree.GF2n.Smith81
