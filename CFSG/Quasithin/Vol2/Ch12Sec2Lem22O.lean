module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22N
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22L

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {G : Type} [Group G] [Finite G]

theorem eq_of_card_four {X V₀ Φ : Subgroup G} (hXV : X ≤ V₀) (hV₀ : Nat.card V₀ = 4)
    (hX1 : X ≠ ⊥) (hΦX : Φ ≤ Subgroup.normalizer (X : Set G))
    (hXC : X ⊓ Subgroup.centralizer (Φ : Set G) = ⊥) : X = V₀ := by
  have hdvd : Nat.card X ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV₀]
    exact Subgroup.card_dvd_of_le hXV
  obtain ⟨k, hk, hXk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  have hx1' : x ≠ 1 := fun h0 => hx1 (Subtype.ext h0)
  interval_cases k
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hXk)) hX1
  ·
    exfalso
    have hxC : x ∈ Subgroup.centralizer (Φ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hfx : f * x * f⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hΦX hf) x).mp hxX
      have hfx1 : f * x * f⁻¹ ≠ 1 := fun h0 => hx1' (by
        have e : x = f⁻¹ * (f * x * f⁻¹) * f := by group
        rw [e, h0]
        group)
      by_contra hne
      have hne' : f * x * f⁻¹ ≠ x := fun h0 => hne (by
        calc f * x = (f * x * f⁻¹) * f := by group
          _ = x * f := by rw [h0])
      classical
      have : Fintype ↥X := Fintype.ofFinite _
      have hs : (({1, ⟨x, hxX⟩, ⟨f * x * f⁻¹, hfx⟩} : Finset ↥X)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · exact fun h0 => hne' (congrArg Subtype.val h0).symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h0 => hx1' (congrArg Subtype.val h0).symm,
            fun h0 => hfx1 (congrArg Subtype.val h0).symm⟩
      have h3 := Finset.card_le_univ ({1, ⟨x, hxX⟩, ⟨f * x * f⁻¹, hfx⟩} : Finset ↥X)
      rw [hs, ← Nat.card_eq_fintype_card, hXk] at h3
      norm_num at h3
    have : x ∈ X ⊓ Subgroup.centralizer (Φ : Set G) := ⟨hxX, hxC⟩
    rw [hXC, Subgroup.mem_bot] at this
    exact hx1' this
  · exact Subgroup.eq_of_le_of_card_ge hXV (by rw [hV₀, hXk]; norm_num)

structure Extra3 (T L V H P U I : Subgroup G) (h : G) : Prop where
  hyp : Hyp1223 G T L V
  noEsc : NoEscape12_2_13 L V
  concl : Concl12_2_20 T L V 3
  pre : Pre12_2_21 T L V H P U I h 3
  UO : U ≤ pCoreOf 2 H
  cardP : Nat.card P = 27
  exp : ∀ x ∈ P, x ^ 3 = 1
  cardΦ : Nat.card ((frattini ↥P).map P.subtype) = 3
  central : ∀ f ∈ (frattini ↥P).map P.subtype, ∀ x ∈ P, f * x = x * f
  ΦV : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G)
  VΦ : ∀ x ∈ V, ∀ f ∈ (frattini ↥P).map P.subtype, x * f * x⁻¹ * f⁻¹ ∈ pCoreOf 2 H
  cent : pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ⊓
        Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G)
  fpf : ∃ X : Subgroup G, X ≠ ⊥ ∧
      X ≤ V ⊓ (pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
      (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem card_inf (e : Extra3 T L V H P U I h) : Nat.card ↥(V ⊓ pCoreOf 2 H) = 4 := by
  have hVO := Lem21.not_le_pCoreOf_of_pre e.pre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -, -⟩ := e.pre
  have hUV : U ⊓ V = pCoreOf 2 H ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V e.UO) inf_le_right
      hidx).resolve_right fun hle => hVO (hle.trans inf_le_left)).symm
  have hidx' : (V ⊓ pCoreOf 2 H).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
  have h1 := Subgroup.relIndex_mul_card (V ⊓ pCoreOf 2 H) V
  rw [hidx', inf_right_comm, inf_idem, e.concl.2.1] at h1
  omega

theorem eq_inf (e : Extra3 T L V H P U I h) :
    V ⊓ pCoreOf 2 H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      (frattini ↥P).map P.subtype ≤ Subgroup.normalizer ((V ⊓ pCoreOf 2 H : Subgroup G) : Set G) ∧
      (V ⊓ pCoreOf 2 H) ⊓
          Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨X, hX1, hXle, hΦX, hXC⟩ := e.fpf
  have hXV : X ≤ V ⊓ pCoreOf 2 H := fun x hx => ⟨(hXle hx).1, (hXle hx).2.1⟩
  have hXeq := eq_of_card_four hXV e.card_inf hX1 hΦX hXC
  rw [← hXeq]
  exact ⟨fun x hx => (hXle hx).2, hΦX, hXC⟩


theorem W_le_center (e : Extra3 T L V H P U I h) :
    conjClosure (V ⊓ pCoreOf 2 H) P ≤
      pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  obtain ⟨-, -, -, -, -, hPH, -⟩ := e.pre
  have hHO : H ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hHA : H ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO hg, B6.le_normalizer_centralizer hHO hg⟩
  refine conjClosure_le fun g hg z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hHA (hPH hg)) z).mp (e.eq_inf.1 hz)

theorem W_elem (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    (∀ a ∈ conjClosure (V ⊓ pCoreOf 2 H) P, ∀ b ∈ conjClosure (V ⊓ pCoreOf 2 H) P,
      a * b = b * a) ∧ ∀ w ∈ conjClosure (V ⊓ pCoreOf 2 H) P, w ^ 2 = 1 := by
  have hWZ := e.W_le_center
  have hc : ∀ a ∈ conjClosure (V ⊓ pCoreOf 2 H) P, ∀ b ∈ conjClosure (V ⊓ pCoreOf 2 H) P,
      a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hWZ hb).2) a (hWZ ha).1
  refine ⟨hc, ?_⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 e.hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  intro w hw
  unfold conjClosure at hw
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨g, -, z, hz, rfl⟩ := hs
    rw [pow_two]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [← pow_two, hV2 z hz.1]; group
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
    rw [Commute.mul_pow (hc a ha b hb) 2, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem le_normalizer_W (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    H ≤ Subgroup.normalizer
      ((conjClosure (V ⊓ pCoreOf 2 H) P : Subgroup G) : Set G) := by
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, -, hhP, hhM, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set W := conjClosure (V ⊓ Q) P with hW
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hWZ : W ≤ Q ⊓ Subgroup.centralizer (Q : Set G) := e.W_le_center
  have hgen : ∀ g ∈ P, ∀ z ∈ V ⊓ Q, g * z * g⁻¹ ∈ W := fun g hg z hz =>
    Subgroup.subset_closure ⟨g, hg, z, hz, rfl⟩
  have hnW : ∀ n : G, n ∈ Subgroup.normalizer (P : Set G) →
      (∀ z ∈ V ⊓ Q, n * z * n⁻¹ ∈ V ⊓ Q) → ∀ w ∈ W, n * w * n⁻¹ ∈ W := by
    intro n hnP hnV w hw
    have hle : W ≤ W.comap (MulAut.conj n).toMonoidHom := conjClosure_le fun g hg z hz => by
      show n * (g * z * g⁻¹) * n⁻¹ ∈ W
      have e1 : n * (g * z * g⁻¹) * n⁻¹ =
          (n * g * n⁻¹) * (n * z * n⁻¹) * (n * g * n⁻¹)⁻¹ := by group
      rw [e1]
      exact hgen _ ((Subgroup.mem_normalizer_iff.mp hnP g).mp hg) _ (hnV z hz)
    exact hle hw
  have hPW : ∀ g ∈ P, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    have hle : W ≤ W.comap (MulAut.conj g).toMonoidHom := conjClosure_le fun g' hg' z hz => by
      show g * (g' * z * g'⁻¹) * g⁻¹ ∈ W
      have e1 : g * (g' * z * g'⁻¹) * g⁻¹ = (g * g') * z * (g * g')⁻¹ := by group
      rw [e1]
      exact hgen _ (P.mul_mem hg hg') z hz
    exact hle hw
  have hTW : ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
    intro t ht w hw
    obtain ⟨q, hq, hqt⟩ := exists_mul_mem_normalizer h331 e.hyp hHs hsol hp hp2 hPp hPH hPi hP1
      (hTH ht)
    have hnT : q * t ∈ T := T.mul_mem (hQT hq) ht
    have h1 : (q * t) * w * (q * t)⁻¹ ∈ W := hnW (q * t) hqt (fun z hz =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hTV hnT) z).mp hz.1,
        (Subgroup.mem_normalizer_iff.mp (hHO (hTH hnT)) z).mp hz.2⟩) w hw
    have hc := (Subgroup.mem_centralizer_iff.mp (hWZ h1).2) _ (Q.inv_mem hq)
    have e1 : t * w * t⁻¹ = q⁻¹ * ((q * t) * w * (q * t)⁻¹) * q := by group
    rw [e1, hc]
    have e2 : (q * t) * w * (q * t)⁻¹ * q⁻¹ * q = (q * t) * w * (q * t)⁻¹ := by group
    rw [e2]
    exact h1
  have hle : P ⊔ T ≤ Subgroup.normalizer (W : Set G) :=
    sup_le (fun g hg => Sec121Swap.mem_normalizer_of_conj_mem (hPW g hg))
      (fun t ht => Sec121Swap.mem_normalizer_of_conj_mem (hTW t ht))
  exact fun g hg => hle (hHPT ▸ hg)

theorem W_inf_centralizer (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) :
    conjClosure (V ⊓ pCoreOf 2 H) P ⊓
      Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨-, -, -, -, -, hPH, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set W := conjClosure (V ⊓ Q) P with hW
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  obtain ⟨hV₀Z, hΦV₀, hV₀C⟩ := e.eq_inf
  obtain ⟨hWc, hW2⟩ := e.W_elem h1222
  have hHW := e.le_normalizer_W h331 h1222
  have hΦP : Φ ≤ P := frattini_map_le P
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥Φ := isCyclic_of_prime_card e.cardΦ
  obtain ⟨⟨z, hzΦ⟩, hgen⟩ := hcyc.exists_generator
  have hmemz : ∀ f ∈ Φ, ∃ k : ℤ, z ^ k = f := fun f hf => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨f, hf⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcz : ∀ w : G, z * w = w * z → w ∈ Subgroup.centralizer (Φ : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    obtain ⟨k, rfl⟩ := hmemz f hf
    exact (Commute.zpow_left hw k)
  have hzW : ∀ w ∈ W, z * w * z⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHW (hPH (hΦP hzΦ))) w).mp hw
  have hS : ∀ s ∈ {x | ∃ g ∈ P, ∃ u ∈ V ⊓ Q, g * u * g⁻¹ = x},
      s * (z * s * z⁻¹) * (z * z * s * (z * z)⁻¹) = 1 := by
    rintro _ ⟨g, hg, u, hu, rfl⟩
    have hzg : z * g = g * z := e.central z hzΦ g hg
    have hzu : z * u * z⁻¹ ∈ V ⊓ Q := (Subgroup.mem_normalizer_iff.mp (hΦV₀ hzΦ) u).mp hu
    have hz2u : z * z * u * (z * z)⁻¹ ∈ V ⊓ Q := by
      have e1 : z * z * u * (z * z)⁻¹ = z * (z * u * z⁻¹) * z⁻¹ := by group
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.mp (hΦV₀ hzΦ) _).mp hzu
    have hV₀c : ∀ a ∈ V ⊓ Q, ∀ b ∈ V ⊓ Q, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hV₀Z hb).2) a (hV₀Z ha).1
    set Nu := u * (z * u * z⁻¹) * (z * z * u * (z * z)⁻¹) with hNu
    have hNuV : Nu ∈ V ⊓ Q := (V ⊓ Q).mul_mem ((V ⊓ Q).mul_mem hu hzu) hz2u
    have hz3 : z ^ 3 = 1 := e.exp z (hΦP hzΦ)
    have hzNu : z * Nu = Nu * z := by
      have h3u : z * (z * z * u * (z * z)⁻¹) * z⁻¹ = u := by
        calc z * (z * z * u * (z * z)⁻¹) * z⁻¹ = z ^ 3 * u * (z ^ 3)⁻¹ := by
              rw [pow_three]; group
          _ = u := by rw [hz3]; group
      have h1 : z * Nu * z⁻¹ = (z * u * z⁻¹) * (z * z * u * (z * z)⁻¹) * u := by
        have e1 : z * Nu * z⁻¹ = (z * u * z⁻¹) * (z * z * u * (z * z)⁻¹) *
            (z * (z * z * u * (z * z)⁻¹) * z⁻¹) := by rw [hNu]; group
        rw [e1, h3u]
      have h2 : (z * u * z⁻¹) * (z * z * u * (z * z)⁻¹) * u = Nu := by
        rw [hNu, hV₀c _ ((V ⊓ Q).mul_mem hzu hz2u) u hu]
        simp only [mul_assoc]
      calc z * Nu = z * Nu * z⁻¹ * z := by group
        _ = Nu * z := by rw [h1, h2]
    have hNu1 : Nu = 1 := by
      have hmem : Nu ∈ (V ⊓ Q) ⊓ Subgroup.centralizer (Φ : Set G) := ⟨hNuV, hcz Nu hzNu⟩
      rw [hV₀C, Subgroup.mem_bot] at hmem
      exact hmem
    have e1 : g * u * g⁻¹ * (z * (g * u * g⁻¹) * z⁻¹) * (z * z * (g * u * g⁻¹) * (z * z)⁻¹) =
        g * Nu * g⁻¹ := by
      have hzg' : z * z * g = g * (z * z) := by
        calc z * z * g = z * (z * g) := by group
          _ = z * (g * z) := by rw [hzg]
          _ = (z * g) * z := by group
          _ = (g * z) * z := by rw [hzg]
          _ = g * (z * z) := by group
      have ea : z * (g * u * g⁻¹) * z⁻¹ = g * (z * u * z⁻¹) * g⁻¹ := by
        calc z * (g * u * g⁻¹) * z⁻¹ = (z * g) * u * (z * g)⁻¹ := by group
          _ = (g * z) * u * (g * z)⁻¹ := by rw [hzg]
          _ = g * (z * u * z⁻¹) * g⁻¹ := by group
      have eb : z * z * (g * u * g⁻¹) * (z * z)⁻¹ = g * (z * z * u * (z * z)⁻¹) * g⁻¹ := by
        calc z * z * (g * u * g⁻¹) * (z * z)⁻¹ = (z * z * g) * u * (z * z * g)⁻¹ := by group
          _ = (g * (z * z)) * u * (g * (z * z))⁻¹ := by rw [hzg']
          _ = g * (z * z * u * (z * z)⁻¹) * g⁻¹ := by group
      rw [ea, eb, hNu]
      group
    rw [e1, hNu1]
    group
  have hfix := eq_one_of_fix_of_norm (S := {x | ∃ g ∈ P, ∃ u ∈ V ⊓ Q, g * u * g⁻¹ = x}) rfl
    hWc hW2 hzW hS
  rw [eq_bot_iff]
  rintro w ⟨hwW, hwC⟩
  rw [Subgroup.mem_bot]
  refine hfix w hwW ?_
  have := (Subgroup.mem_centralizer_iff.mp hwC) z hzΦ
  calc z * w * z⁻¹ = w * z * z⁻¹ := by rw [this]
    _ = w := by group


theorem exists_m (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    ∃ v m : G, v ∈ V ∧ v ∉ pCoreOf 2 H ∧ m * v⁻¹ ∈ pCoreOf 2 H ∧
      m ∈ Subgroup.normalizer (P : Set G) ∧
      (∀ f ∈ (frattini ↥P).map P.subtype, m * f = f * m) ∧
      (∀ x ∈ P, m * x * m⁻¹ * x ∈ (frattini ↥P).map P.subtype) ∧
      m * m ∈ pCoreOf 2 H ∧ (∀ x ∈ P, (m * m) * x * (m * m)⁻¹ = x) ∧
      ∀ r ∈ pCoreOf 2 H, v * r * v⁻¹ * r⁻¹ ∈ V ⊓ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVO := Lem21.not_le_pCoreOf_of_pre e.pre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hPΦ, hhP, hhM, -, -, -, -, -, -, -, hidx,
    -, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 e.hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  have hUV : U ⊓ V = Q ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V e.UO) inf_le_right
      hidx).resolve_right fun hle => hVO (hle.trans inf_le_left)).symm
  have hidx' : (V ⊓ Q).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
  obtain ⟨v, hvV, hvO⟩ := IsConcreteLE.not_le_iff_exists.mp hVO
  have hv2 := hV2 v hvV
  have hvH : v ∈ H := hTH (hVT hvV)
  have hVL := le_pCoreOf_L e.hyp hVT hV2
  obtain ⟨m, hmv, hmP, hmcomm, hminv⟩ := exists_inv_conj_frattini h331 e.hyp hHs hsol hp hp2 hPp
    hPH hPi hHPT hPΦ hVT hTV hVL hidx' hP1 hvV hv2 hvO
  have hPO : ∀ y ∈ P, y ∈ Q → y = 1 := fun y hyP hyO =>
    eq_one_of_mem_of_mem hp hp2 hPp hO2 hyP hyO
  have hmP' : ∀ x ∈ P, m * x * m⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmP x).mp hx
  have hm2O : m * m ∈ Q := by
    obtain ⟨q, hq, rfl⟩ : ∃ q ∈ Q, q * v = m := ⟨m * v⁻¹, hmv, by group⟩
    have e1 : q * v * (q * v) = q * (v * q * v⁻¹) * (v * v) := by group
    rw [e1, ← pow_two v, hv2, mul_one]
    exact Q.mul_mem hq (hconjO v hvH q hq)
  have hm2 : ∀ x ∈ P, (m * m) * x * (m * m)⁻¹ = x := by
    intro x hx
    have h1 : (m * m) * x * (m * m)⁻¹ * x⁻¹ ∈ P := by
      have e1 : (m * m) * x * (m * m)⁻¹ = m * (m * x * m⁻¹) * m⁻¹ := by group
      rw [e1]
      exact P.mul_mem (hmP' _ (hmP' x hx)) (P.inv_mem hx)
    have h2 : (m * m) * x * (m * m)⁻¹ * x⁻¹ ∈ Q := by
      have e1 : (m * m) * x * (m * m)⁻¹ * x⁻¹ = (m * m) * (x * (m * m)⁻¹ * x⁻¹) := by group
      rw [e1]
      exact Q.mul_mem hm2O (hconjO x (hPH hx) _ (Q.inv_mem hm2O))
    exact mul_inv_eq_one.mp (hPO _ h1 h2)
  have hvQ : ∀ r ∈ Q, v * r * v⁻¹ * r⁻¹ ∈ V ⊓ Q := by
    intro r hr
    have h1 : v * r * v⁻¹ * r⁻¹ ∈ V := by
      have h0 : r * v⁻¹ * r⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hTV (hQT hr)) _).mp (V.inv_mem hvV)
      have e1 : v * r * v⁻¹ * r⁻¹ = v * (r * v⁻¹ * r⁻¹) := by group
      rw [e1]
      exact V.mul_mem hvV h0
    exact ⟨h1, Q.mul_mem (hconjO v hvH r hr) (Q.inv_mem hr)⟩
  exact ⟨v, m, hvV, hvO, hmv, hmP, hmcomm, hminv, hm2O, hm2, hvQ⟩

theorem comm_mem_W (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    ∀ x ∈ P, ∀ r ∈ pCoreOf 2 H, x * r * x⁻¹ * r⁻¹ ∈ conjClosure (V ⊓ pCoreOf 2 H) P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHs, -, hp, hp2, hPp, hPH, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set W := conjClosure (V ⊓ Q) P with hW
  obtain ⟨v, m, hvV, -, hmv, hmP, -, hminv, -, hm2, hvQ'⟩ := e.exists_m h331 h1222
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨hVT, -, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hOH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  have hvH : v ∈ H := hTH (hVT hvV)
  have hmP' : ∀ x ∈ P, m * x * m⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmP x).mp hx
  have hHW := e.le_normalizer_W h331 h1222
  have hWQ : W ≤ Q := fun w hw => (e.W_le_center hw).1
  have hWH : W ≤ H := hWQ.trans hOH
  have hvQ : ∀ r ∈ Q, v * r * v⁻¹ * r⁻¹ ∈ W := fun r hr => le_conjClosure _ _ (hvQ' r hr)
  have hinv : ∀ x ∈ P, m * x * m⁻¹ = x⁻¹ → ∀ r ∈ Q, x * r * x⁻¹ * r⁻¹ ∈ W := by
    intro x hx hmx r hr
    have hqQ : m * v⁻¹ ∈ Q := hmv
    have hr₀Q : x * (m * v⁻¹)⁻¹ * x⁻¹ * (m * v⁻¹) ∈ Q :=
      Q.mul_mem (hconjO x (hPH hx) _ (Q.inv_mem hqQ)) hqQ
    have hvx : v * x * v⁻¹ = x⁻¹ * (x * (m * v⁻¹)⁻¹ * x⁻¹ * (m * v⁻¹)) := by
      calc v * x * v⁻¹ = (m * v⁻¹)⁻¹ * (m * x * m⁻¹) * (m * v⁻¹) := by group
        _ = (m * v⁻¹)⁻¹ * x⁻¹ * (m * v⁻¹) := by rw [hmx]
        _ = x⁻¹ * (x * (m * v⁻¹)⁻¹ * x⁻¹ * (m * v⁻¹)) := by group
    have hON : (W.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mpr hHW
    have hR2 : IsPGroup 2 ↥(Q.subgroupOf H) :=
      hO2.of_equiv (Subgroup.subgroupOfEquivOfLe hOH).symm
    have key := comm_mem_of_inv_mod (K := ↥H) (O := W.subgroupOf H) (R := Q.subgroupOf H) hR2
      (v := ⟨v, hvH⟩) (x := ⟨x, hPH hx⟩) (r₀ := ⟨_, hOH hr₀Q⟩)
      (Subtype.ext (by simpa using e.exp x hx))
      (fun r hr => by
        rw [Subgroup.mem_subgroupOf] at hr ⊢
        simpa using hconjO x (hPH hx) _ hr)
      (fun r hr => by
        rw [Subgroup.mem_subgroupOf] at hr ⊢
        simpa using hvQ _ hr)
      (Subgroup.mem_subgroupOf.mpr hr₀Q)
      (Subtype.ext (by simpa using hvx))
    have h1 := key ⟨r, hOH hr⟩ (Subgroup.mem_subgroupOf.mpr hr)
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hgen := mem_closure_inv hp hp2 hPp hmP hminv
  have key : ∀ y ∈ Subgroup.closure {u | ∃ y ∈ P, u = y * (m * y * m⁻¹)⁻¹},
      y ∈ P ∧ ∀ r ∈ Q, y * r * y⁻¹ * r⁻¹ ∈ W := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      have huP : y * (m * y * m⁻¹)⁻¹ ∈ P := P.mul_mem hy (P.inv_mem (hmP' y hy))
      exact ⟨huP, hinv _ huP (conj_eq_inv_of_mem hm2 hy)⟩
    | one => exact ⟨P.one_mem, fun r _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨P.mul_mem iha.1 ihb.1, fun r hr => ?_⟩
      have h1 := ihb.2 r hr
      have h2 := iha.2 r hr
      have h3 : a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hHW (hPH iha.1)) _).mp h1
      have e1 : a * b * r * (a * b)⁻¹ * r⁻¹ =
          (a * (b * r * b⁻¹ * r⁻¹) * a⁻¹) * (a * r * a⁻¹ * r⁻¹) := by group
      rw [e1]
      exact W.mul_mem h3 h2
    | inv a _ iha =>
      refine ⟨P.inv_mem iha.1, fun r hr => ?_⟩
      have hr' : a⁻¹ * r * a ∈ Q := by
        have h0 := hconjO a⁻¹ (H.inv_mem (hPH iha.1)) r hr
        simpa using h0
      have h1 := iha.2 _ hr'
      have e1 : a⁻¹ * r * a⁻¹⁻¹ * r⁻¹ = (a * (a⁻¹ * r * a) * a⁻¹ * (a⁻¹ * r * a)⁻¹)⁻¹ := by
        group
      rw [e1]
      exact W.inv_mem h1
  intro x hx
  exact (key x (hgen x hx)).2


theorem le_normalizer_inf_centralizer (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) :
    H ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ Subgroup.centralizer
      (((frattini ↥P).map P.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, -, hhP, hhM, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set W := conjClosure (V ⊓ Q) P with hW
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hΦP : Φ ≤ P := frattini_map_le P
  have hWZ : W ≤ Q ⊓ Subgroup.centralizer (Q : Set G) := e.W_le_center
  have hcomm := e.comm_mem_W h331 h1222
  have hNP : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer
      ((Subgroup.centralizer (Φ : Set G) : Subgroup G) : Set G) :=
    B6.le_normalizer_centralizer fun g hg =>
      Sec121Swap.mem_normalizer_of_conj_mem fun f hf => conj_mem_frattini hg hf
  have hQD : ∀ q ∈ Q, ∀ d ∈ Q ⊓ Subgroup.centralizer (Φ : Set G),
      q * d * q⁻¹ ∈ Q ⊓ Subgroup.centralizer (Φ : Set G) := by
    intro q hq d hd
    refine ⟨Q.mul_mem (Q.mul_mem hq hd.1) (Q.inv_mem hq), ?_⟩
    show q * d * q⁻¹ ∈ Subgroup.centralizer (Φ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hw : f⁻¹ * q⁻¹ * f⁻¹⁻¹ * q⁻¹⁻¹ ∈ W := hcomm _ (P.inv_mem (hΦP hf)) _ (Q.inv_mem hq)
    have hdw : (f⁻¹ * q⁻¹ * f⁻¹⁻¹ * q⁻¹⁻¹) * d = d * (f⁻¹ * q⁻¹ * f⁻¹⁻¹ * q⁻¹⁻¹) :=
      ((Subgroup.mem_centralizer_iff.mp (hWZ hw).2) d hd.1).symm
    have hdf : f * d = d * f := (Subgroup.mem_centralizer_iff.mp hd.2) f hf
    have e1 : q⁻¹ * f * q = f * (f⁻¹ * q⁻¹ * f⁻¹⁻¹ * q⁻¹⁻¹) := by group
    have hd' : (q⁻¹ * f * q) * d = d * (q⁻¹ * f * q) := by
      rw [e1, mul_assoc, hdw, ← mul_assoc, hdf, mul_assoc]
    calc f * (q * d * q⁻¹) = q * ((q⁻¹ * f * q) * d) * q⁻¹ := by group
      _ = q * (d * (q⁻¹ * f * q)) * q⁻¹ := by rw [hd']
      _ = q * d * q⁻¹ * f := by group
  have hPD : ∀ x ∈ P, ∀ d ∈ Q ⊓ Subgroup.centralizer (Φ : Set G),
      x * d * x⁻¹ ∈ Q ⊓ Subgroup.centralizer (Φ : Set G) := fun x hx d hd =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hHO (hPH hx)) d).mp hd.1,
      (Subgroup.mem_normalizer_iff.mp (hNP (Subgroup.le_normalizer hx)) d).mp hd.2⟩
  have hTD : ∀ t ∈ T, ∀ d ∈ Q ⊓ Subgroup.centralizer (Φ : Set G),
      t * d * t⁻¹ ∈ Q ⊓ Subgroup.centralizer (Φ : Set G) := by
    intro t ht d hd
    obtain ⟨q, hq, hqt⟩ := exists_mul_mem_normalizer h331 e.hyp hHs hsol hp hp2 hPp hPH hPi hP1
      (hTH ht)
    have hn : (q * t) * d * (q * t)⁻¹ ∈ Q ⊓ Subgroup.centralizer (Φ : Set G) :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hHO (H.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 H hq)
        (hTH ht))) d).mp hd.1, (Subgroup.mem_normalizer_iff.mp (hNP hqt) d).mp hd.2⟩
    have e1 : t * d * t⁻¹ = q⁻¹ * ((q * t) * d * (q * t)⁻¹) * q⁻¹⁻¹ := by group
    rw [e1]
    exact hQD _ (Q.inv_mem hq) _ hn
  have hle : P ⊔ T ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (Φ : Set G) : Subgroup G) : Set G) :=
    sup_le (fun g hg => Sec121Swap.mem_normalizer_of_conj_mem (hPD g hg))
      (fun t ht => Sec121Swap.mem_normalizer_of_conj_mem (hTD t ht))
  exact fun g hg => hle (hHPT ▸ hg)

theorem inf_centralizer_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) :
    pCoreOf 2 H ⊓ Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hHs, -, -, -, -, hPH, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set W := conjClosure (V ⊓ Q) P with hW
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hcomm := e.comm_mem_W h331 h1222
  have hWC := e.W_inf_centralizer h331 h1222
  have hHD := e.le_normalizer_inf_centralizer h331 h1222
  obtain ⟨-, -, hV₀C⟩ := e.eq_inf
  intro d hd
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_,
    Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  ·
    have h1 : x * d * x⁻¹ * d⁻¹ ∈ W := hcomm x hx d hd.1
    have h2 : x * d * x⁻¹ * d⁻¹ ∈ Q ⊓ Subgroup.centralizer (Φ : Set G) :=
      (Q ⊓ Subgroup.centralizer (Φ : Set G)).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hHD (hPH hx)) d).mp hd)
        ((Q ⊓ Subgroup.centralizer (Φ : Set G)).inv_mem hd)
    have h3 : x * d * x⁻¹ * d⁻¹ ∈ W ⊓ Subgroup.centralizer (Φ : Set G) := ⟨h1, h2.2⟩
    rw [hWC, Subgroup.mem_bot, mul_inv_eq_one] at h3
    calc x * d = (x * d * x⁻¹) * x := by group
      _ = d * x := by rw [h3]
  ·
    have hdV : d * u⁻¹ * d⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hTV (hQT hd.1)) _).mp (V.inv_mem hu)
    have h1 : u * d * u⁻¹ * d⁻¹ ∈ V := by
      have e1 : u * d * u⁻¹ * d⁻¹ = u * (d * u⁻¹ * d⁻¹) := by group
      rw [e1]
      exact V.mul_mem hu hdV
    have h2 : u * d * u⁻¹ * d⁻¹ ∈ Q ⊓ Subgroup.centralizer (Φ : Set G) :=
      (Q ⊓ Subgroup.centralizer (Φ : Set G)).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hHD (hTH (hVT hu))) d).mp hd)
        ((Q ⊓ Subgroup.centralizer (Φ : Set G)).inv_mem hd)
    have h3 : u * d * u⁻¹ * d⁻¹ ∈ (V ⊓ Q) ⊓ Subgroup.centralizer (Φ : Set G) :=
      ⟨⟨h1, h2.1⟩, h2.2⟩
    rw [hV₀C, Subgroup.mem_bot, mul_inv_eq_one] at h3
    calc u * d = (u * d * u⁻¹) * u := by group
      _ = d * u := by rw [h3]

end Extra3

end Lem22

end CFSG.Quasithin.H13
