module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22O

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {G : Type} [Group G] [Finite G]

@[expose] def commHom {W : Subgroup G} {g : G} (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hgW : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : ↥W →* ↥W where
  toFun w := ⟨w * (g * w * g⁻¹)⁻¹, W.mul_mem w.2 (W.inv_mem (hgW w w.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show (a : G) * b * (g * (a * b) * g⁻¹)⁻¹ =
      (a * (g * a * g⁻¹)⁻¹) * (b * (g * b * g⁻¹)⁻¹)
    have h1 : (b : G) * (g * b * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ =
        (g * a * g⁻¹)⁻¹ * (b * (g * b * g⁻¹)⁻¹) :=
      hWc _ (W.mul_mem b.2 (W.inv_mem (hgW b b.2))) _ (W.inv_mem (hgW a a.2))
    calc (a : G) * b * (g * (a * b) * g⁻¹)⁻¹
        = a * ((b * (g * b * g⁻¹)⁻¹) * (g * a * g⁻¹)⁻¹) := by group
      _ = a * ((g * a * g⁻¹)⁻¹ * (b * (g * b * g⁻¹)⁻¹)) := by rw [h1]
      _ = (a * (g * a * g⁻¹)⁻¹) * (b * (g * b * g⁻¹)⁻¹) := by group)

omit [Finite G] in
theorem relIndex_centralizer_eq {W : Subgroup G} {g : G} (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hgW : ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    (W ⊓ Subgroup.centralizer ({g} : Set G)).relIndex W = Nat.card (commHom hWc hgW).range := by
  rw [← Subgroup.index_ker]
  unfold Subgroup.relIndex
  congr 1
  ext w
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · rintro ⟨-, hw⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    apply Subtype.ext
    show (w : G) * (g * w * g⁻¹)⁻¹ = 1
    rw [← hw]
    group
  · intro hw
    have h1 : (w : G) * (g * w * g⁻¹)⁻¹ = 1 := congrArg Subtype.val hw
    refine ⟨w.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_inv_eq_one] at h1
    calc (w : G) * g = (g * w * g⁻¹) * g := by rw [← h1]
      _ = g * w := by group


omit [Finite G] in
@[expose] def conjAutOf {W : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    MulAut ↥W where
  toFun w := ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg w).mp w.2⟩
  invFun w := ⟨g⁻¹ * w * g, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp w.2
    rwa [inv_inv] at this⟩
  left_inv w := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

theorem not_dvd_card_GL {r : ℕ} (hr : r ≤ 5) : ¬ 27 ∣ Nat.card (GL (Fin r) (ZMod 2)) := by
  rw [Matrix.card_GL_field r, ZMod.card]
  interval_cases r <;> decide

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem exists_inv_noncomm (e : Extra3 T L V H P U I h) {m : G}
    (hmP : m ∈ Subgroup.normalizer (P : Set G))
    (hminv : ∀ x ∈ P, m * x * m⁻¹ * x ∈ (frattini ↥P).map P.subtype)
    (hm2 : ∀ x ∈ P, (m * m) * x * (m * m)⁻¹ = x) :
    ∃ x ∈ P, ∃ y ∈ P, m * x * m⁻¹ = x⁻¹ ∧ m * y * m⁻¹ = y⁻¹ ∧ x * y ≠ y * x := by
  obtain ⟨-, -, hp, hp2, hPp, -⟩ := e.pre
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmP' : ∀ x ∈ P, m * x * m⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmP x).mp hx
  have hgen := mem_closure_inv hp hp2 hPp hmP hminv
  by_contra hno
  push Not at hno
  have hc : ({u | ∃ y ∈ P, u = y * (m * y * m⁻¹)⁻¹} : Set G).Pairwise Commute := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
    have haP : a * (m * a * m⁻¹)⁻¹ ∈ P := P.mul_mem ha (P.inv_mem (hmP' a ha))
    have hbP : b * (m * b * m⁻¹)⁻¹ ∈ P := P.mul_mem hb (P.inv_mem (hmP' b hb))
    exact hno _ haP _ hbP (conj_eq_inv_of_mem hm2 ha) (conj_eq_inv_of_mem hm2 hb)
  have hcomm := Subgroup.isMulCommutative_closure hc
  have hPc : ∀ a b : ↥P, a * b = b * a := fun a b => Subtype.ext (by
    have h1 := congrArg Subtype.val (hcomm.is_comm.comm ⟨a, hgen a a.2⟩ ⟨b, hgen b b.2⟩)
    simpa using h1)
  have hΦ : frattini ↥P = ⊥ := (CFSG.SectionRank.Ccomm.frattini_eq_bot_iff hPp).mpr
    ⟨hPc, fun a => Subtype.ext (by simpa using e.exp a a.2)⟩
  have h3 := e.cardΦ
  rw [hΦ, Subgroup.map_bot, Subgroup.card_bot] at h3
  exact absurd h3 (by norm_num)


theorem card_W (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    Nat.card (conjClosure (V ⊓ pCoreOf 2 H) P) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHs, -, hp, hp2, hPp, hPH, -, -, hPΦ, -, -, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set W := conjClosure (V ⊓ Q) P with hW
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  obtain ⟨v, m, hvV, -, hmv, hmP, hmcomm, hminv, hm2O, hm2, hvQ⟩ := e.exists_m h331 h1222
  obtain ⟨hV₀Z, hΦV₀, hV₀C⟩ := e.eq_inf
  obtain ⟨hWc, hW2⟩ := e.W_elem h1222
  have hHW := e.le_normalizer_W h331 h1222
  have hWZ : W ≤ Q ⊓ Subgroup.centralizer (Q : Set G) := e.W_le_center
  have hWC := e.W_inf_centralizer h331 h1222
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨hVT, -, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hOH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hvH : v ∈ H := hTH (hVT hvV)
  have hmH : m ∈ H := by
    have h0 := H.mul_mem (hOH hmv) hvH
    simpa using h0
  have hΦP : Φ ≤ P := frattini_map_le P
  have hconjW : ∀ g ∈ H, ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHW hg) w).mp hw
  have hmW := hconjW m hmH
  have hesc : ∀ x ∈ P, ∀ u ∈ V, u ≠ 1 → x * u = u * x → x ∈ Φ := by
    intro x hx u hu hu1 hxu
    have hxM := e.noEsc u hu hu1 (Subgroup.mem_centralizer_singleton_iff.mpr hxu)
    show x ∈ Φ
    rw [← hPΦ]
    exact ⟨hx, hxM⟩
  have hwm : ∀ w ∈ W, w * (m * w * m⁻¹)⁻¹ ∈ V ⊓ Q := by
    intro w hw
    have hvw : v * w * v⁻¹ ∈ W := hconjW v hvH w hw
    have hqc : (m * v⁻¹) * (v * w * v⁻¹) = (v * w * v⁻¹) * (m * v⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hWZ hvw).2) _ hmv
    have e1 : m * w * m⁻¹ = v * w * v⁻¹ := by
      calc m * w * m⁻¹ = (m * v⁻¹) * (v * w * v⁻¹) * (m * v⁻¹)⁻¹ := by group
        _ = (v * w * v⁻¹) * (m * v⁻¹) * (m * v⁻¹)⁻¹ := by rw [hqc]
        _ = v * w * v⁻¹ := by group
    rw [e1]
    have h1 := hvQ w (hWZ hw).1
    have e2 : w * (v * w * v⁻¹)⁻¹ = (v * w * v⁻¹ * w⁻¹)⁻¹ := by group
    rw [e2]
    exact (V ⊓ Q).inv_mem h1
  have hm2W : ∀ w ∈ W, (m * m) * w * (m * m)⁻¹ = w := fun w hw => by
    have h0 := (Subgroup.mem_centralizer_iff.mp (hWZ hw).2) _ hm2O
    rw [h0]
    group
  obtain ⟨x, hx, y, hy, hmx, hmy, hxy⟩ := e.exists_inv_noncomm hmP hminv hm2
  have hxΦ : x ∉ Φ := fun h0 => hxy (e.central x h0 y hy)
  have hyΦ : y ∉ Φ := fun h0 => hxy (e.central y h0 x hx).symm
  have hsq : ∀ z ∈ P, ∀ w : G, z * z * w * (z * z)⁻¹ = w → z * w = w * z := by
    intro z hz w h3
    have hz3 : z ^ 3 = 1 := e.exp z hz
    have hz4 : z * z * (z * z) = z := by
      calc z * z * (z * z) = z ^ 3 * z := by rw [pow_three]; group
        _ = z := by rw [hz3, one_mul]
    have h4 : z * w * z⁻¹ = w := by
      calc z * w * z⁻¹ = (z * z * (z * z)) * w * (z * z * (z * z))⁻¹ := by rw [hz4]
        _ = (z * z) * ((z * z) * w * (z * z)⁻¹) * (z * z)⁻¹ := by group
        _ = w := by rw [h3, h3]
    calc z * w = z * w * z⁻¹ * z := by group
      _ = w * z := by rw [h4]
  have hRm := relIndex_centralizer_eq hWc hmW
  set Rm := (commHom hWc hmW).range.map W.subtype with hRmdef
  have hRmcard : Nat.card Rm = Nat.card (commHom hWc hmW).range :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hRmV : Rm ≤ V ⊓ Q := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact hwm w w.2
  have hV₀1 : V ⊓ Q ≠ ⊥ := fun h0 => by
    have h1 := e.card_inf
    rw [← hQ, h0, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀1
  have hu1' : u ≠ 1 := fun h0 => hu1 (Subtype.ext h0)
  have hRm1 : Rm ≠ ⊥ := by
    intro h0
    have hmc : ∀ w ∈ W, m * w * m⁻¹ = w := by
      intro w hw
      have hmem : w * (m * w * m⁻¹)⁻¹ ∈ Rm := ⟨commHom hWc hmW ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
      rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hmem.symm
    have huW : u ∈ W := le_conjClosure _ _ hu
    have hxu : x * u * x⁻¹ ∈ W := Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩
    have h1 := hmc _ hxu
    have h2 : m * (x * u * x⁻¹) * m⁻¹ = x⁻¹ * u * x := by
      calc m * (x * u * x⁻¹) * m⁻¹ = (m * x * m⁻¹) * (m * u * m⁻¹) * (m * x * m⁻¹)⁻¹ := by
            group
        _ = x⁻¹ * u * x := by rw [hmx, hmc u huW]; group
    rw [h2] at h1
    have h3 : x * x * u * (x * x)⁻¹ = u := by
      calc x * x * u * (x * x)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by group
        _ = x * (x⁻¹ * u * x) * x⁻¹ := by rw [h1]
        _ = u := by group
    exact hxΦ (hesc x hx u hu.1 hu1' (hsq x hx u h3))
  have hΦRm : Φ ≤ Subgroup.normalizer (Rm : Set G) := by
    intro f hf
    have hfH : f ∈ H := hPH (hΦP hf)
    refine Sec121Swap.mem_normalizer_of_conj_mem ?_
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    have hfw : f * w * f⁻¹ ∈ W := hconjW f hfH w w.2
    refine ⟨commHom hWc hmW ⟨_, hfw⟩, ⟨⟨_, hfw⟩, rfl⟩, ?_⟩
    show (f * w * f⁻¹) * (m * (f * w * f⁻¹) * m⁻¹)⁻¹ = f * (w * (m * w * m⁻¹)⁻¹) * f⁻¹
    have hfm : f * m = m * f := (hmcomm f hf).symm
    have e1 : m * (f * w * f⁻¹) * m⁻¹ = f * (m * w * m⁻¹) * f⁻¹ := by
      calc m * (f * w * f⁻¹) * m⁻¹ = (m * f) * w * (m * f)⁻¹ := by group
        _ = (f * m) * w * (f * m)⁻¹ := by rw [hfm]
        _ = f * (m * w * m⁻¹) * f⁻¹ := by group
    rw [e1]
    group
  have hRmC : Rm ⊓ Subgroup.centralizer (Φ : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    have h0 : r ∈ (V ⊓ Q) ⊓ Subgroup.centralizer (Φ : Set G) := ⟨hRmV hr.1, hr.2⟩
    rwa [hV₀C] at h0
  have hRmeq := eq_of_card_four hRmV e.card_inf hRm1 hΦRm hRmC
  have hidxm : (W ⊓ Subgroup.centralizer ({m} : Set G)).relIndex W = 4 := by
    rw [hRm, ← hRmcard, hRmeq, e.card_inf]
  have hcard_rel : ∀ K : Subgroup G, K ≤ W → K.relIndex W * Nat.card K = Nat.card W := by
    intro K hKW
    have h1 := Subgroup.relIndex_mul_card K W
    rwa [inf_of_le_left hKW] at h1
  have hCm : 4 * Nat.card ↥(W ⊓ Subgroup.centralizer ({m} : Set G)) = Nat.card W := by
    rw [← hidxm]
    exact hcard_rel _ inf_le_left
  have hmCz : ∀ z ∈ P, m * z * m⁻¹ = z⁻¹ → z ∉ Φ →
      W ⊓ Subgroup.centralizer ({z} : Set G) ≤ W ⊓ Subgroup.centralizer ({m} : Set G) := by
    intro z hz hmz hzΦ w hw
    obtain ⟨hwW, hwz⟩ := Subgroup.mem_inf.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hwz
    refine Subgroup.mem_inf.mpr ⟨hwW, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmz' : m⁻¹ * z * m = z⁻¹ := by
      have h0 : z = m⁻¹ * z⁻¹ * m := by rw [← hmz]; group
      calc m⁻¹ * z * m = (m⁻¹ * z⁻¹ * m)⁻¹ := by group
        _ = z⁻¹ := by rw [← h0]
    have hmz'' : m * z⁻¹ * m⁻¹ = z := by
      calc m * z⁻¹ * m⁻¹ = (m * z * m⁻¹)⁻¹ := by group
        _ = z := by rw [hmz, inv_inv]
    have hzw' : z⁻¹ * w = w * z⁻¹ := by
      calc z⁻¹ * w = z⁻¹ * (w * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * w) * z⁻¹ := by rw [hwz]
        _ = w * z⁻¹ := by group
    have hzc : z * (m * w * m⁻¹) = (m * w * m⁻¹) * z := by
      calc z * (m * w * m⁻¹) = m * (m⁻¹ * z * m) * w * m⁻¹ := by group
        _ = m * (z⁻¹ * w) * m⁻¹ := by rw [hmz']; group
        _ = m * (w * z⁻¹) * m⁻¹ := by rw [hzw']
        _ = (m * w * m⁻¹) * (m * z⁻¹ * m⁻¹) := by group
        _ = (m * w * m⁻¹) * z := by rw [hmz'']
    have hc := hwm w hwW
    by_contra hne
    have hc1 : w * (m * w * m⁻¹)⁻¹ ≠ 1 := fun h0 => hne (by
      rw [mul_inv_eq_one] at h0
      calc w * m = (m * w * m⁻¹) * m := by rw [← h0]
        _ = m * w := by group)
    apply hzΦ
    refine hesc z hz _ hc.1 hc1 ?_
    calc z * (w * (m * w * m⁻¹)⁻¹) = (z * w) * (z * (m * w * m⁻¹))⁻¹ * z := by group
      _ = (w * z) * ((m * w * m⁻¹) * z)⁻¹ * z := by rw [← hwz, hzc]
      _ = w * (m * w * m⁻¹)⁻¹ * z := by group
  have hCz : ∀ z ∈ P, m * z * m⁻¹ = z⁻¹ →
      Nat.card W ≤ 16 * Nat.card ↥(W ⊓ Subgroup.centralizer ({z} : Set G)) := by
    intro z hz hmz
    have hzH : z ∈ H := hPH hz
    have hcard' : Nat.card ↥(W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G)) =
        Nat.card ↥(W ⊓ Subgroup.centralizer ({m} : Set G)) := by
      have hzW := hconjW z hzH
      have hzW' := hconjW z⁻¹ (H.inv_mem hzH)
      refine Nat.card_congr
        { toFun := fun w => ⟨z⁻¹ * w * z, ?_⟩
          invFun := fun w => ⟨z * w * z⁻¹, ?_⟩
          left_inv := fun w => Subtype.ext (by simp [mul_assoc])
          right_inv := fun w => Subtype.ext (by simp [mul_assoc]) }
      · obtain ⟨hwW, hwc⟩ := Subgroup.mem_inf.mp w.2
        rw [Subgroup.mem_centralizer_singleton_iff] at hwc
        refine Subgroup.mem_inf.mpr ⟨by simpa using hzW' _ hwW, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc z⁻¹ * ↑w * z * m = z⁻¹ * (↑w * (z * m * z⁻¹)) * z := by group
          _ = z⁻¹ * ((z * m * z⁻¹) * ↑w) * z := by rw [hwc]
          _ = m * (z⁻¹ * ↑w * z) := by group
      · obtain ⟨hwW, hwc⟩ := Subgroup.mem_inf.mp w.2
        rw [Subgroup.mem_centralizer_singleton_iff] at hwc
        refine Subgroup.mem_inf.mpr ⟨hzW _ hwW, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc z * ↑w * z⁻¹ * (z * m * z⁻¹) = z * (↑w * m) * z⁻¹ := by group
          _ = z * (m * ↑w) * z⁻¹ := by rw [hwc]
          _ = z * m * z⁻¹ * (z * ↑w * z⁻¹) := by group
    have hidx' : (W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G)).relIndex W = 4 := by
      have h1 := hcard_rel _ (inf_le_left :
        W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G) ≤ W)
      rw [hcard', ← hCm] at h1
      have hpos : 0 < Nat.card ↥(W ⊓ Subgroup.centralizer ({m} : Set G)) := Nat.card_pos
      nlinarith
    have hle : (W ⊓ Subgroup.centralizer ({m} : Set G)) ⊓
        (W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G)) ≤
        W ⊓ Subgroup.centralizer ({z} : Set G) := by
      intro w hw
      obtain ⟨hw1', hw2'⟩ := Subgroup.mem_inf.mp hw
      obtain ⟨hwW, hw1⟩ := Subgroup.mem_inf.mp hw1'
      obtain ⟨-, hw2⟩ := Subgroup.mem_inf.mp hw2'
      rw [Subgroup.mem_centralizer_singleton_iff] at hw1 hw2
      refine Subgroup.mem_inf.mpr ⟨hwW, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hmz2 : m * (z * m * z⁻¹) = z⁻¹ * (m * m) * z⁻¹ := by
        have hmz3 : m * z = z⁻¹ * m := by
          calc m * z = (m * z * m⁻¹) * m := by group
            _ = z⁻¹ * m := by rw [hmz]
        calc m * (z * m * z⁻¹) = (m * z) * m * z⁻¹ := by group
          _ = z⁻¹ * m * m * z⁻¹ := by rw [hmz3]
          _ = z⁻¹ * (m * m) * z⁻¹ := by group
      have hw3 : w * (z⁻¹ * (m * m) * z⁻¹) = (z⁻¹ * (m * m) * z⁻¹) * w := by
        rw [← hmz2]
        calc w * (m * (z * m * z⁻¹)) = (w * m) * (z * m * z⁻¹) := by group
          _ = m * (w * (z * m * z⁻¹)) := by rw [hw1]; group
          _ = m * ((z * m * z⁻¹) * w) := by rw [hw2]
          _ = m * (z * m * z⁻¹) * w := by group
      have hw4 : z⁻¹ * w * z ∈ W := by simpa using hconjW z⁻¹ (H.inv_mem hzH) w hwW
      have hm2' := hm2W _ hw4
      have h5 : z⁻¹ * z⁻¹ * w * (z⁻¹ * z⁻¹)⁻¹ = w := by
        have e1 : (z⁻¹ * (m * m) * z⁻¹) * w * (z⁻¹ * (m * m) * z⁻¹)⁻¹ = w := by
          rw [← hw3]
          group
        calc z⁻¹ * z⁻¹ * w * (z⁻¹ * z⁻¹)⁻¹ =
            z⁻¹ * ((m * m) * (z⁻¹ * w * z) * (m * m)⁻¹) * z := by
              rw [hm2']
              simp only [mul_inv_rev, inv_inv, mul_assoc]
          _ = (z⁻¹ * (m * m) * z⁻¹) * w * (z⁻¹ * (m * m) * z⁻¹)⁻¹ := by group
          _ = w := e1
      have h6 := hsq z⁻¹ (P.inv_mem hz) w h5
      calc w * z = z * (z⁻¹ * w) * z := by group
        _ = z * (w * z⁻¹) * z := by rw [h6]
        _ = z * w := by group
    have h1 := Subgroup.relIndex_inf_le (H := W ⊓ Subgroup.centralizer ({m} : Set G))
      (K := W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G)) (L := W)
    rw [hidxm, hidx'] at h1
    have h2 := hcard_rel _ (inf_le_left.trans inf_le_left :
      (W ⊓ Subgroup.centralizer ({m} : Set G)) ⊓
        (W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G)) ≤ W)
    have h3 := Subgroup.card_le_of_le hle
    calc Nat.card W = _ * Nat.card ↥((W ⊓ Subgroup.centralizer ({m} : Set G)) ⊓
          (W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G))) := h2.symm
      _ ≤ 16 * Nat.card ↥((W ⊓ Subgroup.centralizer ({m} : Set G)) ⊓
          (W ⊓ Subgroup.centralizer ({z * m * z⁻¹} : Set G))) := Nat.mul_le_mul_right _ h1
      _ ≤ 16 * Nat.card ↥(W ⊓ Subgroup.centralizer ({z} : Set G)) := Nat.mul_le_mul_left _ h3
  have hxyW : ∀ w ∈ W, x * w = w * x → y * w = w * y → w = 1 := by
    intro w hw hxw hyw
    set c := x * y * x⁻¹ * y⁻¹ with hcdef
    have hcΦ : c ∈ Φ := commutator_mem_frattini_map hp hPp hx hy
    have hc1 : c ≠ 1 := fun h0 => hxy (by
      rw [hcdef, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h0
      exact h0)
    have hcw : c * w = w * c := by
      have hx' : Commute x w := hxw
      have hy' : Commute y w := hyw
      exact ((hx'.mul_left hy').mul_left hx'.inv_left).mul_left hy'.inv_left
    have hzp : Subgroup.zpowers c = Φ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcΦ) ?_
      rw [e.cardΦ, Nat.card_zpowers]
      have h3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one (e.exp c (hΦP hcΦ))
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h4 | h4
      · exact absurd (orderOf_eq_one_iff.mp h4) hc1
      · rw [h4]
    have hwC : w ∈ W ⊓ Subgroup.centralizer (Φ : Set G) := by
      refine ⟨hw, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
      rw [← hzp] at hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      exact (Commute.zpow_left hcw k)
    rw [hWC, Subgroup.mem_bot] at hwC
    exact hwC
  have hprod : Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) *
      Nat.card ↥(W ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      Nat.card ↥(W ⊓ Subgroup.centralizer ({m} : Set G)) := by
    rw [← Nat.card_prod]
    have hxm := hmCz x hx hmx hxΦ
    have hym := hmCz y hy hmy hyΦ
    refine Nat.card_le_card_of_injective
      (fun ab => ⟨(ab.1 : G) * ab.2, (W ⊓ Subgroup.centralizer ({m} : Set G)).mul_mem
        (hxm ab.1.2) (hym ab.2.2)⟩) ?_
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have hab' : a * b = a' * b' := congrArg Subtype.val hab
    have hd : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab']
        _ = b' * b⁻¹ := by group
    have hdx : a'⁻¹ * a ∈ W ⊓ Subgroup.centralizer ({x} : Set G) :=
      (W ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
        ((W ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem ha') ha
    have hdy : b' * b⁻¹ ∈ W ⊓ Subgroup.centralizer ({y} : Set G) :=
      (W ⊓ Subgroup.centralizer ({y} : Set G)).mul_mem hb'
        ((W ⊓ Subgroup.centralizer ({y} : Set G)).inv_mem hb)
    rw [← hd] at hdy
    have h1 := hxyW _ hdx.1
      ((Subgroup.mem_centralizer_singleton_iff.mp hdx.2).symm)
      ((Subgroup.mem_centralizer_singleton_iff.mp hdy.2).symm)
    have ha_eq : a = a' := by
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    have hb_eq : b = b' := by
      rw [ha_eq] at hab'
      exact mul_left_cancel hab'
    subst ha_eq hb_eq
    rfl
  have hx16 := hCz x hx hmx
  have hy16 := hCz y hy hmy
  have hle64 : Nat.card W ≤ 64 := by
    have hpos : 0 < Nat.card W := Nat.card_pos
    nlinarith
  have hWp : IsPGroup 2 ↥W := hO2.to_le (fun w hw => (hWZ hw).1)
  obtain ⟨r, hr⟩ := hWp.exists_card_eq
  let φ : ↥P →* MulAut ↥W :=
    { toFun := fun g => conjAutOf (hHW (hPH g.2))
      map_one' := by ext w; simp [conjAutOf]
      map_mul' := fun a b => by
        ext w
        simp only [conjAutOf, MulAut.mul_apply, MulEquiv.coe_mk, Equiv.coe_fn_mk,
          Subgroup.coe_mul]
        group }
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨g, hg⟩ hgk
    rw [MonoidHom.mem_ker] at hgk
    have hgw : ∀ w ∈ W, g * w = w * g := fun w hw => by
      have h1 := congrArg (fun α : MulAut ↥W => ((α ⟨w, hw⟩ : ↥W) : G)) hgk
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, conjAutOf, MulEquiv.coe_mk,
        Equiv.coe_fn_mk, MulAut.one_apply] at h1
      calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [h1]
    have huW : u ∈ W := le_conjClosure _ _ hu
    have hgΦ : g ∈ Φ := hesc g hg u hu.1 hu1' (hgw u huW)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    by_contra hg1
    have hzp : Subgroup.zpowers g = Φ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgΦ) ?_
      rw [e.cardΦ, Nat.card_zpowers]
      have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (e.exp g hg)
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h4 | h4
      · exact absurd (orderOf_eq_one_iff.mp h4) hg1
      · rw [h4]
    have huC : u ∈ W ⊓ Subgroup.centralizer (Φ : Set G) := by
      refine ⟨huW, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
      rw [← hzp] at hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      exact (Commute.zpow_left (hgw u huW) k)
    rw [hWC, Subgroup.mem_bot] at huC
    exact hu1' huC
  have h27 : 27 ∣ Nat.card (MulAut ↥W) := by
    rw [← e.cardP]
    exact Subgroup.card_dvd_of_injective φ hφ
  have hcommW : ∀ a b : ↥W, a * b = b * a := fun a b =>
    Subtype.ext (hWc a a.2 b b.2)
  have hpowW : ∀ a : ↥W, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hW2 a a.2)
  obtain ⟨e₀⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcommW hpowW hr
  have hGL : Nat.card (MulAut ↥W) = Nat.card (GL (Fin r) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e₀).toEquiv
  rw [hGL] at h27
  have hr6 : r ≤ 6 := by
    rw [hr] at hle64
    by_contra h7
    push Not at h7
    have : 2 ^ 7 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h7
    omega
  have hr6' : 6 ≤ r := by
    by_contra h5
    push Not at h5
    exact not_dvd_card_GL (by omega) h27
  rw [hr, show r = 6 by omega]
  norm_num

end Extra3

end Lem22

end CFSG.Quasithin.H13
