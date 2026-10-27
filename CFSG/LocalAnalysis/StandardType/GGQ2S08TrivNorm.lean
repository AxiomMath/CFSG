module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TrivSetup
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoPart
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CrossComm
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

private def ggQ2s08t1c_cent {G : Type} [Group G] (p : ℕ) (X : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧
    ∀ x ∈ X, ⁅x, g⁆ ∈ LargeEvenPPrimeCoreOf p X}
  one_mem' := ⟨Subgroup.one_mem _, by intro x hx; simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hgO⟩ ⟨hhN, hhO⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun x hx => ?_⟩
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅x, g⁆ ∈ LargeEvenPPrimeCoreOf p X := hgO x hx
    have h2 : g * ⁅x, h⁆ * g⁻¹ ∈ LargeEvenPPrimeCoreOf p X :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_largeEvenPPrimeCoreOf hgN) _).mp
        (hhO x hx)
    have hgoal : (⁅x, g⁆ * g * ⁅x, h⁆ * g⁻¹) = ⁅x, g⁆ * (g * ⁅x, h⁆ * g⁻¹) := by
      group
    rw [hgoal]
    exact Subgroup.mul_mem _ h1 h2
  inv_mem' := by
    rintro g ⟨hgN, hgO⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun x hx => ?_⟩
    rw [commutatorElement_inv_right, ← commutatorElement_inv x g]
    have h1 : ⁅x, g⁆ ∈ LargeEvenPPrimeCoreOf p X := hgO x hx
    simpa using (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.inv_mem _ hgN)) _).mp
        (Subgroup.inv_mem _ h1)

private theorem ggQ2s08t1c_cent_commutator {G : Type} [Group G] {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ ggQ2s08t1c_cent (G := G) p X) :
    ⁅X, Subgroup.zpowers g⁆ ≤ LargeEvenPPrimeCoreOf p X := by
  rw [Subgroup.commutator_le]
  intro x hx h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Subgroup.zpow_mem _ hg k).2 x hx

private theorem ggQ2s08t1c_cent_mem_commutator {G : Type} [Group G] {p : ℕ}
    {X : Subgroup G} {g : G} (hgN : g ∈ Subgroup.normalizer (X : Set G))
    (hg : ⁅X, Subgroup.zpowers g⁆ ≤ LargeEvenPPrimeCoreOf p X) :
    g ∈ ggQ2s08t1c_cent (G := G) p X := by
  refine ⟨hgN, fun x hx => ?_⟩
  exact (Subgroup.commutator_le.mp hg) x hx g (Subgroup.mem_zpowers g)

private theorem ggQ2s08t1c_conj_commutator_gen {G : Type} [Group G] [Finite G] {p : ℕ}
    {X : Subgroup G} {g d : G}
    (h : ⁅X, Subgroup.zpowers d⁆ ≤ LargeEvenPPrimeCoreOf p X) :
    ⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers (g * d * g⁻¹)⁆ ≤
      LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) := by
  have hmap : (⁅X, Subgroup.zpowers d⁆).map (MulAut.conj g).toMonoidHom =
      ⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers (g * d * g⁻¹)⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    simp
  rw [← hmap]
  calc (⁅X, Subgroup.zpowers d⁆).map (MulAut.conj g).toMonoidHom
      ≤ (LargeEvenPPrimeCoreOf p X).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono h
    _ = LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) :=
        (largeEvenPPrimeCoreOf_map_conj p X g).symm

private theorem ggQ2s08t1c_map_conj_map_conj_inv {G : Type} [Group G] (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [map_conj_map_conj, inv_mul_cancel,
    show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext x; simp]
  exact Subgroup.map_id X

private theorem ggQ2s08t1c_map_conj_inv_mul_conj {G : Type} [Group G] (X : Subgroup G) (g z : G) :
    X.map (MulAut.conj (g⁻¹ * z * g)).toMonoidHom =
      ((X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj z).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [map_conj_map_conj X g z, map_conj_map_conj X (z * g) g⁻¹]
  exact congrArg (fun w : G => X.map (MulAut.conj w).toMonoidHom) (mul_assoc g⁻¹ z g)

private theorem ggQ2s08t1c_cent_conj_iff {G : Type} [Group G] [Finite G] {p : ℕ}
    {X : Subgroup G} {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G)) (z : G) :
    z ∈ ggQ2s08t1c_cent p X ↔ g * z * g⁻¹ ∈ ggQ2s08t1c_cent p X := by
  have hgXmap : X.map (MulAut.conj g).toMonoidHom = X :=
    mem_normalizer_iff_map_conj.mp hgX
  have hgXinv : X.map (MulAut.conj g⁻¹).toMonoidHom = X :=
    mem_normalizer_iff_map_conj.mp (Subgroup.inv_mem _ hgX)
  constructor
  · intro hz
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgX hz.1) (Subgroup.inv_mem _ hgX), ?_⟩
    intro w hw
    have h := ggQ2s08t1c_conj_commutator_gen (g := g) (d := z)
      (ggQ2s08t1c_cent_commutator hz)
    rw [hgXmap] at h
    exact (Subgroup.commutator_le.mp h) w hw (g * z * g⁻¹) (Subgroup.mem_zpowers _)
  · intro hz
    have hmem : g⁻¹ * (g * z * g⁻¹) * g ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgX) hz.1) hgX
    have hz_eq : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [hz_eq] at hmem
    refine ⟨hmem, fun w hw => ?_⟩
    have h := ggQ2s08t1c_conj_commutator_gen (X := X) (g := g⁻¹) (d := g * z * g⁻¹)
      (ggQ2s08t1c_cent_commutator hz)
    rw [hgXinv] at h
    have hzpow : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rw [hzpow] at h
    exact (Subgroup.commutator_le.mp h) w hw z (Subgroup.mem_zpowers z)

private noncomputable def ggQ2s08t1c_shift {G : Type} [Group G] {Bs : Subgroup G}
    (hcomm : ∀ a b : ↥Bs, a * b = b * a) (φ : MulAut ↥Bs) : ↥Bs →* ↥Bs where
  toFun b := b⁻¹ * φ b
  map_one' := by simp
  map_mul' := fun a b => by
    have h1 : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    have h2 : φ (a * b) = φ a * φ b := map_mul φ a b
    have hkey : b⁻¹ * (a⁻¹ * φ a) = (a⁻¹ * φ a) * b⁻¹ := hcomm b⁻¹ (a⁻¹ * φ a)
    rw [h1, h2]
    calc b⁻¹ * a⁻¹ * (φ a * φ b)
        = b⁻¹ * (a⁻¹ * (φ a * φ b)) := by group
      _ = b⁻¹ * ((a⁻¹ * φ a) * φ b) := by group
      _ = (b⁻¹ * (a⁻¹ * φ a)) * φ b := by group
      _ = ((a⁻¹ * φ a) * b⁻¹) * φ b := by rw [hkey]
      _ = (a⁻¹ * φ a) * (b⁻¹ * φ b) := by group

theorem ggQ2s08_triv_normalizes (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) {g : G} {φ : MulAut ↥Bs}
    (hInd : GGQ2Ind Bs g φ) (hR : GGIsReflection p φ) {u : ↥Bs} (hu : (u : G) ∈ D)
    (hu1 : u ≠ 1) (htr : GGTrivialLine p B x D J u) (hφu : φ u = u) :
    ∃ Z : Subgroup G, Z ≤ Bs ∧ x ∈ Z ∧ Z ≤ Subgroup.centralizer (J : Set G) ∧
      g ∈ Subgroup.normalizer (Z : Set G) := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hDJ⟩ := hcfg
  have hprime : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hprime⟩
  have hBsabel : IsElemAbelian p Bs := hBstar.2.1
  have hBsC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBle : B ≤ Bs := hBstar.1
  have hxB : x ∈ B := hI.2.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hBle hxB
  have huBs : (u : G) ∈ Bs := hBle (hDJ.1.1 hu)
  have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := hInd.1
  obtain ⟨X, hXcomp, hJX, hBsN, hxc, hZJmem⟩ :=
    ggQ2s08_triv_setup hLB hP hS hp hu hu1 htr
  let Z : Subgroup G := Bs ⊓ ggQ2s08t1c_cent p X
  have hZle : Z ≤ Bs := inf_le_left
  have hxZ : x ∈ Z := ⟨hxBs, ggQ2s08t1c_cent_mem_commutator (hBsN hxBs) hxc⟩
  have hZJ : Z ≤ Subgroup.centralizer (J : Set G) := fun z hz =>
    hZJmem z hz.1 (ggQ2s08t1c_cent_commutator hz.2)
  by_cases hgX : g ∈ Subgroup.normalizer (X : Set G)
  · have hZnorm : g ∈ Subgroup.normalizer (Z : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      have hBsiff : z ∈ Bs ↔ g * z * g⁻¹ ∈ Bs := Subgroup.mem_normalizer_iff.mp hgN z
      have hCentiff : z ∈ ggQ2s08t1c_cent p X ↔ g * z * g⁻¹ ∈ ggQ2s08t1c_cent p X :=
        ggQ2s08t1c_cent_conj_iff hgX z
      constructor
      · rintro ⟨hzB, hzC⟩
        exact ⟨hBsiff.mp hzB, hCentiff.mp hzC⟩
      · rintro ⟨hzB, hzC⟩
        exact ⟨hBsiff.mpr hzB, hCentiff.mpr hzC⟩
    exact ⟨Z, hZle, hxZ, hZJ, hZnorm⟩
  · exfalso
    have hgu : g * (u : G) * g⁻¹ = (u : G) := by
      have h := hInd.2 u
      rw [hφu] at h
      exact h.symm
    have hHmap : (Subgroup.centralizer ({(u : G)} : Set G)).map
        (MulAut.conj g).toMonoidHom = Subgroup.centralizer ({(u : G)} : Set G) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hgu]
    let X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom
    have hX'comp : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X' := by
      have h := largeEvenPComponent_map_conj' (g := g) hXcomp
      rw [hHmap] at h
      exact h
    have hXne : X' ≠ X := by
      intro h
      exact hgX (mem_normalizer_iff_map_conj.mpr h)
    have hBsN' : Bs ≤ Subgroup.normalizer (X' : Set G) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨(g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹, ?_, ?_⟩
        · change (g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹ ∈ X
          simpa only [inv_inv, mul_assoc] using (Subgroup.mem_normalizer_iff.mp
            (hBsN ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) b).mp hb)) x).mp hx
        · change (MulAut.conj g) ((g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹) = b * y * b⁻¹
          rw [show (MulAut.conj g) ((g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹) =
                b * ((MulAut.conj g) x) * b⁻¹ by
              simp only [MulAut.conj_apply]; group,
            show (MulAut.conj g) x = y from hxy]
      · rintro ⟨x, hx, hxy⟩
        refine ⟨(g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g), ?_, ?_⟩
        · change (g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g) ∈ X
          have hmem := (Subgroup.mem_normalizer_iff.mp
            (hBsN ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) b⁻¹).mp
              (Bs.inv_mem hb))) x).mp hx
          simpa only [mul_inv_rev, inv_inv, mul_assoc] using hmem
        · change (MulAut.conj g) ((g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g)) = y
          rw [show (MulAut.conj g) ((g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g)) =
                b⁻¹ * ((MulAut.conj g) x) * b by
              simp only [MulAut.conj_apply]; group,
            show (MulAut.conj g) x = b * y * b⁻¹ from hxy]
          group
    let hshift : ↥Bs →* ↥Bs := ggQ2s08t1c_shift (fun a b => Subtype.ext (hBsC a a.2 b b.2)) φ
    let C : Subgroup G := hshift.range.map Bs.subtype
    have hhker : ∀ b : ↥Bs, b ∈ hshift.ker ↔ φ b = b := by
      intro b
      rw [MonoidHom.mem_ker]
      show b⁻¹ * φ b = 1 ↔ φ b = b
      rw [inv_mul_eq_one, eq_comm]
    have hker : Nat.card hshift.ker = Nat.card {b : ↥Bs // φ b = b} :=
      Nat.card_congr (Equiv.subtypeEquivRight hhker)
    haveI : Nonempty {b : ↥Bs // φ b = b} := ⟨⟨1, map_one φ⟩⟩
    have hrange : Nat.card hshift.range = p := by
      have hcard := Subgroup.card_ker_mul_card_range hshift
      have hcard2 : Nat.card ↥hshift.ker * Nat.card ↥hshift.range =
          Nat.card ↥hshift.ker * p := by
        rw [hcard, ← hR.2, hker]
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard2
    have hCcard : Nat.card C = p := by
      rw [Subgroup.card_map_of_injective Bs.subtype_injective, hrange]
    have hCBs : C ≤ Bs := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨w, -, rfl⟩
      exact w.2
    let Z' : Subgroup G := Bs ⊓ ggQ2s08t1c_cent p X'
    have hsub : Z' ≤ Z ⊔ C := by
      intro z' hz'
      obtain ⟨hz'B, hz'C⟩ := hz'
      have hzB : g⁻¹ * z' * g ∈ Bs := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z').mp hz'B
        simpa only [inv_inv] using h
      have hzC : g⁻¹ * z' * g ∈ ggQ2s08t1c_cent p X := by
        refine ⟨?_, ?_⟩
        · rw [mem_normalizer_iff_map_conj]
          rw [ggQ2s08t1c_map_conj_inv_mul_conj X g z']
          have hz'map : (X.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj z').toMonoidHom = X.map (MulAut.conj g).toMonoidHom :=
            mem_normalizer_iff_map_conj.mp hz'C.1
          rw [hz'map]
          exact ggQ2s08t1c_map_conj_map_conj_inv X g
        · intro w hw
          have h := ggQ2s08t1c_conj_commutator_gen (X := X') (g := g⁻¹) (d := z')
            (ggQ2s08t1c_cent_commutator hz'C)
          dsimp only [X'] at h
          rw [ggQ2s08t1c_map_conj_map_conj_inv X g] at h
          simpa only [inv_inv] using
            (Subgroup.commutator_le.mp h) w hw (g⁻¹ * z' * g⁻¹⁻¹) (Subgroup.mem_zpowers _)
      have hzZ : g⁻¹ * z' * g ∈ Z := ⟨hzB, hzC⟩
      have hφz : ((hshift ⟨g⁻¹ * z' * g, hzB⟩ : ↥Bs) : G) =
          (g⁻¹ * z' * g)⁻¹ * z' := by
        show (((⟨g⁻¹ * z' * g, hzB⟩ : ↥Bs)⁻¹ * φ ⟨g⁻¹ * z' * g, hzB⟩ : ↥Bs) : G) =
          (g⁻¹ * z' * g)⁻¹ * z'
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hInd.2]
        group
      have hz'eq : z' = (g⁻¹ * z' * g) * ((hshift ⟨g⁻¹ * z' * g, hzB⟩ : ↥Bs) : G) := by
        rw [hφz]; group
      have hxrange : hshift ⟨g⁻¹ * z' * g, hzB⟩ ∈ hshift.range :=
        MonoidHom.mem_range.mpr ⟨⟨g⁻¹ * z' * g, hzB⟩, rfl⟩
      have hmemC : ((hshift ⟨g⁻¹ * z' * g, hzB⟩ : ↥Bs) : G) ∈ C :=
        Subgroup.mem_map_of_mem Bs.subtype hxrange
      rw [hz'eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hzZ) (Subgroup.mem_sup_right hmemC)
    have hBH : Bs ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hBsC b hb (u : G) huBs
    have hBp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
    have hA : ∀ ν ∈ ggAutomizer J Bs, (∀ b : ↥Bs, (b : G) ∈ Z → ν b = b) ∧
        ∀ b : ↥Bs, ((b⁻¹ * ν b : ↥Bs) : G) ∈ Z ⊔ C := by
      intro ν hν
      rw [mem_ggAutomizer_iff] at hν
      obtain ⟨n, hnJ, hnN, hnφ⟩ := hν
      have hnX : n ∈ X := hJX hnJ
      have hcross := ggQ2s08_cross_commutes hXcomp hX'comp hXne.symm hBp hBH hBsN hBsN'
        hnX hnN
      constructor
      · intro b hbZ
        have hbBs : (b : G) ∈ Bs := hZle hbZ
        have hbz : ⁅X, Subgroup.zpowers (b : G)⁆ ≤ LargeEvenPPrimeCoreOf p X :=
          ggQ2s08t1c_cent_commutator hbZ.2
        have hfix := hcross.1 (b : G) hbBs hbz
        apply Subtype.ext
        rw [hnφ b]
        exact hfix
      · intro b
        have hbBs : (b : G) ∈ Bs := b.2
        obtain ⟨hbBs', hbcent⟩ := hcross.2 (b : G) hbBs
        have hbZ' : ⁅n, (b : G)⁆ ∈ Z' :=
          ⟨hbBs', ggQ2s08t1c_cent_mem_commutator (hBsN' hbBs') hbcent⟩
        have hmem : ⁅n, (b : G)⁆ ∈ Z ⊔ C := hsub hbZ'
        have heq : ((b⁻¹ * ν b : ↥Bs) : G) = ⁅n, (b : G)⁆ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hnφ b]
          have h1 : n * (b : G) * n⁻¹ = ⁅n, (b : G)⁆ * (b : G) := by
            rw [commutatorElement_def]; group
          have hcommB : (b : G)⁻¹ * ⁅n, (b : G)⁆ = ⁅n, (b : G)⁆ * (b : G)⁻¹ :=
            hBsC (b : G)⁻¹ (by simpa using Bs.inv_mem b.2) ⁅n, (b : G)⁆ hbBs'
          rw [h1, ← mul_assoc, hcommB, mul_assoc, inv_mul_cancel, mul_one]
        rw [heq]
        exact hmem
    have hSZ : Nat.card ↥(Z ⊔ C) ≤ p * Nat.card ↥Z := by
      have hcommZC : ∀ a ∈ Z, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
        hBsC a (hZle ha) b (hCBs hb)
      have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z C hcommZC).1
      have hpos : 0 < Nat.card ↥(Z ⊓ C) := Nat.card_pos
      calc Nat.card ↥(Z ⊔ C)
          ≤ Nat.card ↥(Z ⊔ C) * Nat.card ↥(Z ⊓ C) := Nat.le_mul_of_pos_right _ hpos
        _ = Nat.card ↥Z * Nat.card ↥C := hcard
        _ = p * Nat.card ↥Z := by rw [hCcard, Nat.mul_comm]
    exact (ggQ2s08_two_part hp hBsabel le_sup_left (sup_le hZle hCBs) hSZ
      (ggAutomizer J Bs) hA) hCav

end CFSG.StandardType

end
