module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux6
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux1

public section

open CFSG.Open
open scoped commutatorElement Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] {p : ℕ}

structure Setup (p : ℕ) (A X D D₂ N L R X₁ X₂ W : Subgroup Γ) [(D₂.subgroupOf D).Normal] :
    Prop where
  hyp : Hyp p A X D D₂ N L R
  pair : (X₁, X₂) ∈ iPairsY A X D₂
  sol_eq : sol X = ⊥
  ne_bot : X ≠ ⊥
  le_K : W ≤ kOf X
  le_X₁ : W ≤ X₁
  perf : Group.IsPerfect ↥W
  adm : Admits (X₁ ⊔ D ⊔ A) W
  sup_eq : W ⊔ X₂ = X₁
  inf_eq : W ⊓ X₂ = ⊥

theorem mem_normalizer_sup {A' B' : Subgroup Γ} {x : Γ}
    (hA : x ∈ Subgroup.normalizer (A' : Set Γ)) (hB : x ∈ Subgroup.normalizer (B' : Set Γ)) :
    x ∈ Subgroup.normalizer ((A' ⊔ B' : Subgroup Γ) : Set Γ) :=
  Admits.sup (Q := Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hA)
    (Subgroup.zpowers_le.mpr hB) (Subgroup.mem_zpowers x)

theorem isMulCommutative_map {Δ : Type*} [Group Δ] {T : Subgroup Γ} [IsMulCommutative T]
    (f : Γ →* Δ) : IsMulCommutative ↥(T.map f) := by
  refine isMulCommutative_iff.mpr ?_
  rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
  have := congrArg (fun z : T => f (z : Γ)) (mul_comm' (⟨a, ha⟩ : T) ⟨b, hb⟩)
  exact Subtype.ext (by simpa using this)

theorem comm_mem_of_mem_normalizer {K : Subgroup Γ} {x y : Γ} (hx : x ∈ K)
    (hy : y ∈ Subgroup.normalizer (K : Set Γ)) : ⁅x, y⁆ ∈ K := by
  rw [commutatorElement_def]
  have h1 : y * x⁻¹ * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hy _).mp (inv_mem hx)
  have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [this]
  exact mul_mem hx h1

namespace Setup

variable [Finite Γ] {A X D D₂ N L R X₁ X₂ W : Subgroup Γ} [(D₂.subgroupOf D).Normal]
  (S : Setup p A X D D₂ N L R X₁ X₂ W)

include S

omit [Finite Γ] in
theorem cen : cenIn X (A : Set Γ) = D := S.hyp.cen

omit [Finite Γ] in
theorem admits_DA_W : Admits (D ⊔ A) W :=
  (sup_le (D_le_H X₁ D A) (A_le_H X₁ D A)).trans S.adm

omit [Finite Γ] in
theorem admits_cenDA_W : Admits (cenIn X (A : Set Γ) ⊔ A) W := by
  rw [S.cen]
  exact S.admits_DA_W

omit [Finite Γ] in
theorem lemma213Hyp : Lemma213.Hyp p A X W :=
  ⟨S.hyp.near, S.sol_eq, S.ne_bot, S.le_K, S.admits_cenDA_W, S.perf⟩

omit [Finite Γ] in
theorem X₁_le_X : X₁ ≤ X := Thm33a.pair_le S.pair

omit [Finite Γ] in
theorem X₂_le_X₁ : X₂ ≤ X₁ := Thm33a.pair_le₂ S.pair

omit [Finite Γ] in
theorem D₂_eq : X₂ ⊓ D = D₂ := by
  have := Thm33a.pair_inf S.pair
  rwa [S.cen] at this

omit [Finite Γ] in
theorem D₂_le_X₂ : D₂ ≤ X₂ := S.D₂_eq ▸ inf_le_left

omit [Finite Γ] in
theorem admits_X₁ : Admits (X₁ ⊔ D ⊔ A) X₁ := by
  have := Thm33a.pair_admits_H S.pair
  rwa [S.cen] at this

omit [Finite Γ] in
theorem admits_X₂ : Admits (X₁ ⊔ D ⊔ A) X₂ := by
  have := Thm33a.pair_admits_H₂ S.pair
  rwa [S.cen] at this

omit [Finite Γ] in
theorem comm_W_X₂ {w x : Γ} (hw : w ∈ W) (hx : x ∈ X₂) : w * x = x * w :=
  (Thm33a.commute_of_inf_eq_bot ((R_le_H X₁ D A).trans S.adm)
    ((R_le_H X₁ D A).trans S.admits_X₂) S.le_X₁ S.X₂_le_X₁ S.inf_eq hw hx).eq

omit [Finite Γ] in
theorem D₂_comm_W {s w : Γ} (hs : s ∈ D₂) (hw : w ∈ W) : s * w = w * s :=
  (S.comm_W_X₂ hw (S.D₂_le_X₂ hs)).symm

omit [Finite Γ] in
theorem mem_D₂_of_comm {x : Γ} (hx : x ∈ D) (hc : ∀ w ∈ W, w * x = x * w) : x ∈ D₂ :=
  Thm33a.mem_Y_of_commute S.pair S.le_X₁ S.sup_eq (by rw [S.cen]; exact hx) hc

omit [Finite Γ] in
theorem D₂_le_cenIn_W : D₂ ≤ cenIn X (W : Set Γ) := fun _ hs =>
  Subgroup.mem_inf.mpr ⟨S.hyp.D₂_le_X hs, Subgroup.mem_centralizer_iff.mpr fun _ hw =>
    (S.D₂_comm_W hs hw).symm⟩

theorem admits_K : Admits (D ⊔ A) (kOf X) := by
  have := S.lemma213Hyp.admits_DA_kOf
  rwa [S.cen] at this

theorem admits_k1 : Admits (D ⊔ A) (k1 X W) :=
  Lemma213.admits_cenIn S.admits_K S.admits_DA_W

theorem admits_k2 : Admits (D ⊔ A) (k2 X W) :=
  Lemma213.admits_cenIn S.admits_K S.admits_k1

theorem K_le_normalizer_k1
    : kOf X ≤ Subgroup.normalizer (k1 X W : Set Γ) := by
  have hdp := S.lemma213Hyp.isDirectPair
  rw [← hdp.sup_eq]
  refine sup_le Subgroup.le_normalizer fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hc : ∀ x ∈ k1 X W, y * x * y⁻¹ = x := fun x hx => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hdp.commute x hx y hy).symm
  have hc' : ∀ x ∈ k1 X W, y⁻¹ * x * y = x := fun x hx => by
    have h1 := hdp.commute x hx y hy
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [h1]
      _ = x := by group
  constructor
  · intro hz
    rw [hc z hz]
    exact hz
  · intro hz
    have := hc' _ hz
    rw [show y⁻¹ * (y * z * y⁻¹) * y = z by group] at this
    rw [this]
    exact hz

theorem tTwo_map_conj {J : Subgroup Γ} (hJ : J ∈ Lemma213.tTwo X W) {c : Γ} (hc : c ∈ A) :
    J.map (MulAut.conj c).toMonoidHom ∈ Lemma213.tTwo X W := by
  have HW := S.lemma213Hyp
  have hss := HW.semisimpleAction
  have hJ' : J.map (MulAut.conj c).toMonoidHom ∈ lcal (kOf X) := hss.permutes_lcal c hc J hJ.1
  refine ⟨hJ', ?_⟩
  rw [projIn_map_conj HW.hK (hss.permutes_lcal c hc) (hss.permutes_lcal c⁻¹ (inv_mem hc)) hJ.1
    (HW.admits_A_W hc), hJ.2]

theorem exists_conj_eq_of_cen
    {s : Γ} (hs : s ∈ cenIn X (W : Set Γ)) {J : Subgroup Γ}
    (hJ : J ∈ Lemma213.tTwo X W) :
    ∃ c ∈ A, J.map (MulAut.conj s).toMonoidHom = J.map (MulAut.conj c).toMonoidHom := by
  have HW := S.lemma213Hyp
  have hK := HW.hK
  have hSA := HW.semisimpleAction
  obtain ⟨hsG, hsW⟩ := Subgroup.mem_inf.1 hs
  have hsN : s ∈ Subgroup.normalizer (kOf X : Set Γ) :=
    Lemma213.mem_normalizer_kOf S.sol_eq (Subgroup.le_normalizer hsG)
  have hperm : ∀ J' ∈ lcal (kOf X), J'.map (MulAut.conj s).toMonoidHom ∈ lcal (kOf X) :=
    fun J' hJ' => map_conj_mem_lcal hJ' hsN
  have hsmear : smear J A ≠ ⊥ := fun h0 => hSA.fittingSubgroupOf_smear_ne_bot hJ.1
    (le_bot_iff.1 ((Subgroup.map_subtype_le _).trans h0.le))
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hsmear
  have hxW : x ∈ W := HW.smear_le_W hJ hx
  have hxK : x ∈ kOf X := S.le_K hxW
  have hsx : s * x * s⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hsW x hxW).symm
  have hc1 : hK.coord hJ.1 ⟨x, hxK⟩ ≠ 1 := by
    intro h1
    have h2 : x ∈ sSup (lcal (kOf X) \ {J}) := (hK.coord_eq_one_iff hJ.1 ⟨x, hxK⟩).1 h1
    have h3 : x ∈ smear J A ⊓ sSup (lcal (kOf X) \ {J}) := Subgroup.mem_inf.2 ⟨hx, h2⟩
    rw [hSA.smear_inf_sSup hJ.1] at h3
    exact hx1 (Subtype.ext (Subgroup.mem_bot.1 h3))
  have key := hK.coord_conj hperm hJ.1 hxK
  have e : (⟨s * x * s⁻¹, hK.conj_mem hperm hxK⟩ : ↥(kOf X)) = ⟨x, hxK⟩ := Subtype.ext hsx
  rw [e] at key
  by_contra hcon
  push Not at hcon
  have hmem : x ∈ sSup (lcal (kOf X) \ {J.map (MulAut.conj s).toMonoidHom}) := by
    have h1 : x ∈ orbitClosure J A := smear_le_orbitClosure J A hx
    rw [← Thm210g.sSup_orbSet] at h1
    have hsub : Thm210g.orbSet A J ⊆ lcal (kOf X) \ {J.map (MulAut.conj s).toMonoidHom} := by
      rintro K ⟨c, hc, rfl⟩
      exact ⟨hSA.permutes_lcal c hc J hJ.1, fun h => hcon c hc (Set.mem_singleton_iff.1 h).symm⟩
    exact sSup_le_sSup hsub h1
  have h0 := (hK.coord_eq_one_iff (hperm J hJ.1) ⟨x, hxK⟩).2 hmem
  apply hc1
  rw [h0] at key
  have h2 : s * ((hK.coord hJ.1 ⟨x, hxK⟩ : J) : Γ) * s⁻¹ = 1 := by
    rw [← key]
    rfl
  apply Subtype.ext
  rw [mul_inv_eq_one] at h2
  simpa using h2

theorem D₂_normalizes
    {J : Subgroup Γ} (hJ : J ∈ Lemma213.tTwo X W) {s : Γ} (hs : s ∈ D₂) :
    s ∈ Subgroup.normalizer (J : Set Γ) := by
  have HW := S.lemma213Hyp
  have hSA := HW.semisimpleAction
  have hAp : IsPGroup p A := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A
    S.hyp.near.elemAbelian
  have hcop : Nat.Coprime p (Nat.card D₂) :=
    S.hyp.near.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le S.hyp.D₂_le_X)
  have hA : ∀ g ∈ A, ∀ J' ∈ Thm210g.orbSet A J,
      J'.map (MulAut.conj g).toMonoidHom ∈ Thm210g.orbSet A J := by
    rintro g hg _ ⟨b, hb, rfl⟩
    exact ⟨g * b, mul_mem hg hb, Thm210.map_conj_map_conj J b g⟩
  have hC : ∀ g ∈ D₂, ∀ J' ∈ Thm210g.orbSet A J,
      J'.map (MulAut.conj g).toMonoidHom ∈ Thm210g.orbSet A J := by
    rintro g hg _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hgc⟩ := S.exists_conj_eq_of_cen (S.D₂_le_cenIn_W hg) (S.tTwo_map_conj hJ hb)
    exact ⟨c * b, mul_mem hc hb, hgc.trans (Thm210.map_conj_map_conj J b c)⟩
  have htrans : ∀ J₁ ∈ Thm210g.orbSet A J, ∀ J₂ ∈ Thm210g.orbSet A J,
      ∃ a ∈ A, J₂ = J₁.map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact ⟨c * b⁻¹, mul_mem hc (inv_mem hb), by
      rw [Thm210.map_conj_map_conj, inv_mul_cancel_right]⟩
  exact normalizes_of_isPGroup_transitive_conj S.hyp.near.prime hAp hcop S.hyp.admits_A_D₂
    (fun _ hg => Lemma212.map_conj_mem_of_mem_sup hC hA hg) htrans s hs J
    (Thm210g.self_mem_orbSet A J)

theorem D₂_comm_k2
    {s y : Γ} (hs : s ∈ D₂) (hy : y ∈ k2 X W) : s * y = y * s := by
  have HW := S.lemma213Hyp
  have hK := HW.hK
  have hperm : ∀ J' ∈ lcal (kOf X), J'.map (MulAut.conj s).toMonoidHom ∈ lcal (kOf X) :=
    fun J' hJ' => map_conj_mem_lcal hJ' (Lemma213.mem_normalizer_kOf S.sol_eq
      (Subgroup.le_normalizer (S.hyp.D₂_le_X hs)))
  have hJc : ∀ J ∈ Lemma213.tTwo X W, J ≤ Subgroup.centralizer ({s} : Set Γ) := by
    intro J hJ t ht
    have hsJ : s ∈ Subgroup.normalizer (J : Set Γ) := S.D₂_normalizes hJ hs
    have htP : t ∈ projIn (lcal (kOf X)) J W := hJ.2.symm ▸ ht
    obtain ⟨u, huW, hut⟩ := (hK.mem_projIn_iff hJ.1).1 htP
    have hsu : s * (u : Γ) * s⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact S.D₂_comm_W hs huW
    have h1 := Thm210g.coord_conj_of_normalizer hK hperm hJ.1 hsJ u
    have e : (⟨s * (u : Γ) * s⁻¹, hK.conj_mem hperm u.2⟩ : ↥(kOf X)) = u := Subtype.ext hsu
    rw [e, hut] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * s = (s * t * s⁻¹) * s := by rw [← h1]
      _ = s * t := by group
  have hK2 : k2 X W ≤ Subgroup.centralizer ({s} : Set Γ) := by
    rw [HW.k2_eq]
    exact sSup_le hJc
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hK2 hy)).symm

theorem comm_D₂_mem_k1
    {x s : Γ} (hx : x ∈ kOf X) (hs : s ∈ D₂) : ⁅x, s⁆ ∈ k1 X W := by
  have hdp := S.lemma213Hyp.isDirectPair
  have hx' : x ∈ k1 X W ⊔ k2 X W := by rw [hdp.sup_eq]; exact hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (mem_sup_iff_of_commute hdp.commute).mp hx'
  have hsN : s ∈ Subgroup.normalizer (k1 X W : Set Γ) :=
    S.admits_k1 (Subgroup.mem_sup_left (S.hyp.D₂_le_D hs))
  have h1 : s * x₂ = x₂ * s := S.D₂_comm_k2 hs hx₂
  have h2 : x₂ * s * x₂⁻¹ = s := by rw [← h1]; group
  have : ⁅x₁ * x₂, s⁆ = x₁ * (s * x₁⁻¹ * s⁻¹) := by
    rw [commutatorElement_def]
    calc x₁ * x₂ * s * (x₁ * x₂)⁻¹ * s⁻¹ = x₁ * (x₂ * s * x₂⁻¹) * x₁⁻¹ * s⁻¹ := by group
      _ = x₁ * (s * x₁⁻¹ * s⁻¹) := by rw [h2]; group
  rw [this]
  exact mul_mem hx₁ ((Subgroup.mem_normalizer_iff.mp hsN _).mp (inv_mem hx₁))

theorem X_le_normalizer_K : X ≤ Subgroup.normalizer (kOf X : Set Γ) := fun _ hg =>
  Lemma213.mem_normalizer_kOf S.sol_eq (Subgroup.le_normalizer hg)

theorem comm_Ds_mem
    {x d : Γ} (hxR : x ∈ R) (hxK : x ∈ kOf X) (hd : d ∈ fittingPre D D₂) :
    ⁅x, d⁆ ∈ (N ⊓ kOf X) ⊔ k1 X W := by
  have H := S.hyp
  have hXK := S.X_le_normalizer_K
  have hHN : R ⊔ D ⊔ A ≤ Subgroup.normalizer (N : Set Γ) := H.H_le_N
  have hdS : d ∈ D₂ ⊔ N ⊔ L := by
    rw [H.prod.2.2.1]
    exact Subgroup.mem_sup_left hd
  have hDL : D₂ ⊔ N ≤ Subgroup.normalizer (L : Set Γ) :=
    sup_le (H.D₂_le_D.trans ((D_le_H R D A).trans H.H_le_L)) (H.nN.1.trans H.H_le_L)
  have hd' : d ∈ ((D₂ ⊔ N : Subgroup Γ) : Set Γ) * (L : Set Γ) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDL]
    exact hdS
  obtain ⟨u, hu, ℓ, hℓ, rfl⟩ := hd'
  have hD₂N : D₂ ≤ Subgroup.normalizer (N : Set Γ) :=
    H.D₂_le_D.trans ((D_le_H R D A).trans hHN)
  have hu' : u ∈ (D₂ : Set Γ) * (N : Set Γ) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hD₂N]
    exact hu
  obtain ⟨d₂, hd₂, n, hn, rfl⟩ := hu'
  have hxN : x ∈ Subgroup.normalizer (N : Set Γ) := H.R_normalizes_N hxR
  have hE : ⁅x, n⁆ ∈ N ⊓ kOf X := by
    refine Subgroup.mem_inf.mpr ⟨?_, comm_mem_of_mem_normalizer hxK (hXK (H.hN hn))⟩
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hxN n).mp hn) (inv_mem hn)
  have hF : ⁅x, ℓ⁆ ∈ N ⊓ kOf X :=
    Subgroup.mem_inf.mpr ⟨H.R_comm hxR hℓ, comm_mem_of_mem_normalizer hxK (hXK (H.hL hℓ))⟩
  have hc : ⁅x, d₂⁆ ∈ k1 X W := S.comm_D₂_mem_k1 hxK hd₂
  have hd₂N : d₂ ∈ Subgroup.normalizer ((N ⊓ kOf X : Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hD₂N hd₂, hXK (S.hyp.D₂_le_X hd₂)⟩
  have hnN : n ∈ Subgroup.normalizer ((N ⊓ kOf X : Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨(H.nN.1.trans hHN) hn, hXK (H.hN hn)⟩
  have hdn : d₂ * n ∈ Subgroup.normalizer ((N ⊓ kOf X : Subgroup Γ) : Set Γ) := mul_mem hd₂N hnN
  have h1 : d₂ * ⁅x, n⁆ * d₂⁻¹ ∈ N ⊓ kOf X := (Subgroup.mem_normalizer_iff.mp hd₂N _).mp hE
  have h2 : d₂ * n * ⁅x, ℓ⁆ * (d₂ * n)⁻¹ ∈ N ⊓ kOf X :=
    (Subgroup.mem_normalizer_iff.mp hdn _).mp hF
  have hid : ⁅x, d₂ * n * ℓ⁆ = ⁅x, d₂⁆ * (d₂ * ⁅x, n⁆ * d₂⁻¹) * (d₂ * n * ⁅x, ℓ⁆ * (d₂ * n)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left h1))
    (Subgroup.mem_sup_left h2)

theorem V_le_Ds {J : Subgroup Γ} (hJ : J ∈ lcal (kOf X)) :
    CFSG.fittingSubgroupOf (smear J A) ≤ fittingPre D D₂ := by
  have hss := S.lemma213Hyp.semisimpleAction
  have hCD : cenIn (kOf X) (A : Set Γ) ≤ D := by
    rw [← S.cen]
    exact inf_le_inf_right _ (kOf_le X)
  have hDA : D ≤ Subgroup.normalizer (A : Set Γ) := fun d hd => by
    have hd' : d ∈ cenIn X (A : Set Γ) := by rw [S.cen]; exact hd
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hd').2
  have hdc : D ≤ Subgroup.normalizer ((cenIn (kOf X) (A : Set Γ) : Subgroup Γ) : Set Γ) :=
    Lemma213.admits_cenIn (S.admits_K.mono_left le_sup_left) hDA
  have h2 : CFSG.fittingSubgroupOf (cenIn (kOf X) (A : Set Γ)) ≤ CFSG.fittingSubgroupOf D := by
    refine Thm210.le_fittingSubgroupOf_of_nilpotent ((Subgroup.map_subtype_le _).trans hCD) ?_
      (Thm210.isNilpotent_fittingSubgroupOf _)
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => Thm210.fittingSubgroupOf_conj_mem_of_mem_normalizer (hdc hd) hx, fun hx => by
      have := Thm210.fittingSubgroupOf_conj_mem_of_mem_normalizer (hdc (inv_mem hd)) hx
      simpa [mul_assoc] using this⟩
  have h3 : CFSG.fittingSubgroupOf D ≤ fittingPre D D₂ :=
    le_fittingPre_of_nilpotent (Subgroup.map_subtype_le _)
      (Thm210.le_normalizer_fittingSubgroupOf D) (Thm210.isNilpotent_fittingSubgroupOf D)
  exact (hss.fittingSubgroupOf_smear_le hJ).trans (h2.trans h3)

theorem smear_le_k2
    {J : Subgroup Γ} (hJ : J ∈ Lemma213.tTwo X W) : smear J A ≤ k2 X W := by
  refine (smear_le_orbitClosure J A).trans ?_
  rw [← Thm210g.sSup_orbSet, S.lemma213Hyp.k2_eq]
  refine sSup_le_sSup ?_
  rintro K ⟨c, hc, hK⟩
  rw [hK]
  exact S.tTwo_map_conj hJ hc

theorem admits_X' : Admits (D ⊔ A) ((N ⊓ kOf X) ⊔ k1 X W) := by
  have hN : Admits (D ⊔ A) N :=
    (sup_le (D_le_H R D A) (A_le_H R D A)).trans S.hyp.H_le_N
  exact (hN.inf S.admits_K).sup S.admits_k1

theorem not_V_le
    {J : Subgroup Γ} (hJ : J ∈ Lemma213.tTwo X W) :
    ¬ CFSG.fittingSubgroupOf (smear J A) ≤ (N ⊓ kOf X) ⊔ k1 X W := by
  intro hle
  have HW := S.lemma213Hyp
  have hss := HW.semisimpleAction
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (hss.fittingSubgroupOf_smear_ne_bot hJ.1)
  have heV : e ∈ smear J A := Subgroup.map_subtype_le _ he
  have heD : e ∈ cenIn X (A : Set Γ) := by
    have h1 := hss.smear_le_cenIn hJ.1 heV
    exact Subgroup.mem_inf.mpr ⟨kOf_le X (Subgroup.mem_inf.mp h1).1, (Subgroup.mem_inf.mp h1).2⟩
  have hAK : Admits A (kOf X) := S.admits_K.mono_left le_sup_right
  have key : ((N ⊓ kOf X) ⊔ k1 X W) ⊓ cenIn X (A : Set Γ) ≤ k1 X W :=
    inf_cenIn_sup_le S.hyp.near (D₂ := k1 X W) (inf_le_right.trans (kOf_le X))
      (inf_le_left.trans (kOf_le X)) (S.hyp.admits_A_N.inf hAK)
      (S.admits_k1.mono_left le_sup_right)
      (inf_le_right.trans S.K_le_normalizer_k1)
      (fun a ha => by
        have h1 := Subgroup.mem_inf.mp ha
        have h2 := Subgroup.mem_inf.mp h1.1
        have haD : a ∈ D := by rw [← S.cen]; exact h1.2
        have haD₂ : a ∈ D₂ := S.hyp.ND (Subgroup.mem_inf.mpr ⟨haD, h2.1⟩)
        exact Subgroup.mem_inf.mpr ⟨h2.2, Subgroup.mem_centralizer_iff.mpr fun w hw =>
          (S.D₂_comm_W haD₂ hw).symm⟩)
      inf_le_left
  have hek1 : e ∈ k1 X W := key (Subgroup.mem_inf.mpr ⟨hle he, heD⟩)
  have hek2 : e ∈ k2 X W := S.smear_le_k2 hJ heV
  have hbot : e ∈ k1 X W ⊓ k2 X W := Subgroup.mem_inf.mpr ⟨hek1, hek2⟩
  rw [HW.isDirectPair.inf_eq_bot, Subgroup.mem_bot] at hbot
  exact he1 (Subtype.ext hbot)

omit [Finite Γ] in
theorem cenIn_K_le_D : cenIn (kOf X) (A : Set Γ) ≤ D := by
  rw [← S.cen]
  exact inf_le_inf_right _ (kOf_le X)

theorem projIn_le_fProd
    {J : Subgroup Γ} (hJ : J ∈ Lemma213.tTwo X W) :
    projIn (lcal (kOf X)) J (R ⊓ kOf X) ≤ projIn (lcal (kOf X)) J (fProd A (kOf X)) := by
  have HW := S.lemma213Hyp
  have hss := HW.semisimpleAction
  have H := S.hyp
  have hX'adm : Admits (cenIn (kOf X) (A : Set Γ) ⊔ A) ((N ⊓ kOf X) ⊔ k1 X W) :=
    S.admits_X'.mono_left (sup_le_sup_right S.cenIn_K_le_D A)
  have hmain := hss.projIn_sectionCentralizer_le hJ.1 hX'adm
    (le_sup_left : (N ⊓ kOf X) ⊔ k1 X W ≤ ((N ⊓ kOf X) ⊔ k1 X W) ⊔ fittingPre D D₂)
    (S.not_V_le hJ) ((S.V_le_Ds hJ.1).trans le_sup_right)
  refine (Thm210.projIn_mono J ?_).trans hmain
  intro x hx
  obtain ⟨hxR, hxK⟩ := Subgroup.mem_inf.mp hx
  have hDsN' : fittingPre D D₂ ≤
      Subgroup.normalizer (((N ⊓ kOf X) ⊔ k1 X W : Subgroup Γ) : Set Γ) :=
    fittingPre_le.trans (le_sup_left.trans S.admits_X')
  have hcom : ∀ x ∈ R ⊓ kOf X, ∀ d ∈ fittingPre D D₂, ⁅x, d⁆ ∈ (N ⊓ kOf X) ⊔ k1 X W :=
    fun x hx d hd => S.comm_Ds_mem (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2 hd
  have hnormX' : ∀ x ∈ R ⊓ kOf X,
      x ∈ Subgroup.normalizer (((N ⊓ kOf X) ⊔ k1 X W : Subgroup Γ) : Set Γ) := fun x hx =>
    mem_normalizer_sup (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨H.R_normalizes_N (Subgroup.mem_inf.mp hx).1,
        Subgroup.le_normalizer (Subgroup.mem_inf.mp hx).2⟩)
      (S.K_le_normalizer_k1 (Subgroup.mem_inf.mp hx).2)
  have hprod : ∀ y ∈ ((N ⊓ kOf X) ⊔ k1 X W) ⊔ fittingPre D D₂,
      ∃ d ∈ fittingPre D D₂, ∃ ξ ∈ (N ⊓ kOf X) ⊔ k1 X W, y = d * ξ := by
    intro y hy
    have hy' : y ∈ (fittingPre D D₂ : Set Γ) * (((N ⊓ kOf X) ⊔ k1 X W : Subgroup Γ) : Set Γ) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDsN', sup_comm]
      exact hy
    obtain ⟨d, hd, ξ, hξ, rfl⟩ := hy'
    exact ⟨d, hd, ξ, hξ, rfl⟩
  have hfwd : ∀ x ∈ R ⊓ kOf X, ∀ y ∈ ((N ⊓ kOf X) ⊔ k1 X W) ⊔ fittingPre D D₂,
      x * y * x⁻¹ ∈ ((N ⊓ kOf X) ⊔ k1 X W) ⊔ fittingPre D D₂ := by
    intro x hx y hy
    obtain ⟨d, hd, ξ, hξ, rfl⟩ := hprod y hy
    have h1 : x * (d * ξ) * x⁻¹ = (⁅x, d⁆ * d) * (x * ξ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (hcom x hx d hd)) (Subgroup.mem_sup_right hd))
      (Subgroup.mem_sup_left ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hnormX' x hx) ξ).mp hξ
  have hnormY : ∀ x ∈ R ⊓ kOf X, x ∈ Subgroup.normalizer
      ((((N ⊓ kOf X) ⊔ k1 X W) ⊔ fittingPre D D₂ : Subgroup Γ) : Set Γ) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfwd x hx y hy, fun hy => ?_⟩
    have := hfwd x⁻¹ (inv_mem hx) _ hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this
  have hcommY : ∀ x ∈ R ⊓ kOf X, ∀ y ∈ ((N ⊓ kOf X) ⊔ k1 X W) ⊔ fittingPre D D₂,
      ⁅x, y⁆ ∈ (N ⊓ kOf X) ⊔ k1 X W := by
    intro x hx y hy
    obtain ⟨d, hd, ξ, hξ, rfl⟩ := hprod y hy
    have h1 : ⁅x, d * ξ⁆ = ⁅x, d⁆ * (d * ⁅x, ξ⁆ * d⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    refine mul_mem (hcom x hx d hd) ?_
    have hxξ : ⁅x, ξ⁆ ∈ (N ⊓ kOf X) ⊔ k1 X W := by
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hnormX' x hx) ξ).mp hξ) (inv_mem hξ)
    exact (Subgroup.mem_normalizer_iff.mp (hDsN' hd) _).mp hxξ
  exact Subgroup.mem_inf.mpr ⟨hxK, mem_sectionCentralizer_iff.mpr
    ⟨hnormX' x hx, hnormY x hx, hcommY x hx⟩⟩

theorem smear_le_RK {J : Subgroup Γ} (hJ : J ∈ Lemma213.tOne X W) :
    smear J A ≤ R ⊓ kOf X := by
  have HW := S.lemma213Hyp
  have hss := HW.semisimpleAction
  intro y hy
  have hyD : y ∈ D := S.cenIn_K_le_D (hss.smear_le_cenIn hJ.1 hy)
  have hyk1 : y ∈ k1 X W := HW.smear_le_k1 hJ hy
  have hyD₂ : y ∈ D₂ := S.mem_D₂_of_comm hyD fun w hw =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyk1).2 w hw)
  exact Subgroup.mem_inf.mpr ⟨S.hyp.D₂_le_R hyD₂, (Subgroup.mem_inf.mp hyk1).1⟩

theorem R_normalizes_k1
    : R ≤ Subgroup.normalizer (k1 X W : Set Γ) := by
  have HW := S.lemma213Hyp
  have hss := HW.semisimpleAction
  have H := S.hyp
  have hmap : ∀ r ∈ R, ∀ J ∈ Lemma213.tOne X W,
      J.map (MulAut.conj r).toMonoidHom ∈ Lemma213.tOne X W := by
    intro r hr J hJ
    have hrN : r ∈ Subgroup.normalizer (kOf X : Set Γ) := S.X_le_normalizer_K (H.hR hr)
    have hrN' : r⁻¹ ∈ Subgroup.normalizer (kOf X : Set Γ) := inv_mem hrN
    have hJ' : J.map (MulAut.conj r).toMonoidHom ∈ lcal (kOf X) := map_conj_mem_lcal hJ.1 hrN
    by_contra hnot
    have hJ'two : J.map (MulAut.conj r).toMonoidHom ∈ Lemma213.tTwo X W := by
      rw [HW.tTwo_eq_diff]
      exact ⟨hJ', hnot⟩
    have hF : projIn (lcal (kOf X)) (J.map (MulAut.conj r).toMonoidHom) (fProd A (kOf X)) ≤
        CFSG.fittingSubgroupOf (kJ A (J.map (MulAut.conj r).toMonoidHom)) :=
      (hss.le_fProd_iff.mp le_rfl).2 _ hJ'
    have := hss.isMulCommutative_fittingSubgroupOf_kJ hJ'
    have hab : IsMulCommutative ↥(projIn (lcal (kOf X)) (J.map (MulAut.conj r).toMonoidHom)
        (R ⊓ kOf X)) := Thm210.isMulCommutative_of_le ((S.projIn_le_fProd hJ'two).trans hF)
    have hrR : r⁻¹ ∈ Subgroup.normalizer (R : Set Γ) := inv_mem (Subgroup.le_normalizer hr)
    have hrP : r⁻¹ ∈ Subgroup.normalizer ((R ⊓ kOf X : Subgroup Γ) : Set Γ) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hrR, hrN'⟩
    have hconj := projIn_map_conj HW.hK (fun J' hJ'' => map_conj_mem_lcal hJ'' hrN')
      (fun J' hJ'' => map_conj_mem_lcal hJ'' (inv_mem hrN')) hJ' hrP
    rw [Lemma212.map_conj_map_conj_inv] at hconj
    have hab' : IsMulCommutative ↥(projIn (lcal (kOf X)) J (R ⊓ kOf X)) := by
      rw [hconj]
      exact isMulCommutative_map _
    have hle : projIn (lcal (kOf X)) J (smear J A) ≤ projIn (lcal (kOf X)) J (R ⊓ kOf X) :=
      Thm210.projIn_mono J (S.smear_le_RK hJ)
    rw [hss.projIn_smear hJ.1] at hle
    have := Thm210.isMulCommutative_of_le hle
    exact hss.not_isNilpotent_cenIn hJ.1 inferInstance
  have hconj : ∀ r ∈ R, ∀ x ∈ k1 X W, r * x * r⁻¹ ∈ k1 X W := by
    intro r hr x hx
    rw [HW.k1_eq] at hx ⊢
    have : sSup (Lemma213.tOne X W) ≤
        (sSup (Lemma213.tOne X W)).comap (MulAut.conj r).toMonoidHom := by
      refine sSup_le fun J hJ z hz => ?_
      have : (MulAut.conj r).toMonoidHom z ∈ J.map (MulAut.conj r).toMonoidHom := ⟨z, hz, rfl⟩
      exact le_sSup (hmap r hr J hJ) this
    exact this hx
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj r hr x hx, fun hx => ?_⟩
  have := hconj r⁻¹ (inv_mem hr) _ hx
  rwa [show r⁻¹ * (r * x * r⁻¹) * r⁻¹⁻¹ = x by group] at this

omit [Finite Γ] in
theorem chief : IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂ := by
  have := Thm33a.pair_chief S.pair
  rwa [S.cen] at this

theorem k1_eq_bot (hXeq : X = X₁ ⊔ R ⊔ D)
    (key : ∀ M : Subgroup Γ, M ≤ X → Admits X M → Admits A M → M ⊓ X₁ ≤ X₂ → M = ⊥) :
    k1 X W = ⊥ := by
  have HW := S.lemma213Hyp
  have hk1X : k1 X W ≤ X := inf_le_left.trans (kOf_le X)
  have hX₁N : X₁ ≤ Subgroup.normalizer (k1 X W : Set Γ) :=
    Lemma213.admits_cenIn (fun _ hg => S.X_le_normalizer_K (S.X₁_le_X hg))
      ((R_le_H X₁ D A).trans S.adm)
  have hDN : D ≤ Subgroup.normalizer (k1 X W : Set Γ) := S.admits_k1.mono_left le_sup_left
  have hXN : X ≤ Subgroup.normalizer (k1 X W : Set Γ) :=
    hXeq.le.trans (sup_le (sup_le hX₁N S.R_normalizes_k1) hDN)
  have hAN : Admits A (k1 X W) := S.admits_k1.mono_left le_sup_right
  have hHk1 : Admits (X₁ ⊔ D ⊔ A) (k1 X W) := sup_le (sup_le hX₁N hDN) hAN
  have hk1X₁ : k1 X W ⊓ X₁ ≤ X₂ := by
    rcases Thm33a.chief_dichotomy S.chief (hHk1.inf S.admits_X₁) inf_le_right with h | h
    · exact h
    · refine (Thm33a.false_of_commute S.pair inf_le_right S.le_X₁ h S.sup_eq ?_).elim
      intro m hm w hw
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm).1.2 w hw).symm
  exact key (k1 X W) hk1X hXN hAN hk1X₁

theorem D₂_eq_bot
    (hk1 : k1 X W = ⊥) : D₂ = ⊥ := by
  have h := lemma213c S.hyp.near S.sol_eq S.ne_bot S.le_K S.admits_cenDA_W S.perf hk1
  exact le_bot_iff.mp (h ▸ S.D₂_le_cenIn_W)

theorem tTwo_eq_lcal
    (hk1 : k1 X W = ⊥) : Lemma213.tTwo X W = lcal (kOf X) := by
  have HW := S.lemma213Hyp
  have hemp : Lemma213.tOne X W = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun J hJ => ?_
    have := HW.le_k1_of_mem_tOne hJ
    rw [hk1, le_bot_iff] at this
    exact Lemma213.ne_bot_of_mem_lcal hJ.1 this
  rw [HW.tTwo_eq_diff, hemp, Set.sdiff_empty]

end Setup

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35
