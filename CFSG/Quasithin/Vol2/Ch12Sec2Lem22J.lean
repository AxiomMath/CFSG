module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22H
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {G : Type} [Group G] [Finite G]

theorem facts_of_pre (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1216 : Stmt12_2_16)
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hyp : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Concl12_2_20 T L V n)
    (hpre : Pre12_2_21 T L V H P U I h p) (hUO : U ≤ pCoreOf 2 H) (hPnc : ¬ IsCyclic ↥P) :
    (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G) ∧
      (∀ x ∈ V, ∀ f ∈ (frattini ↥P).map P.subtype, x * f * x⁻¹ * f⁻¹ ∈ pCoreOf 2 H) ∧
      pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ⊓
          Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
        Subgroup.centralizer (P : Set G) ∧
      ∃ X : Subgroup G, X ≠ ⊥ ∧
        X ≤ V ⊓ (pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
        (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (X : Set G) ∧
        X ⊓ Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hPΦ, hhP, hhM, -, -, -, -, -, -, -, hidx,
    -, -⟩ := hpre
  have : Fact p.Prime := ⟨hp⟩
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hΦP : Φ ≤ P := frattini_map_le P
  have hhΦ : h ∉ Φ := fun h0 => hhM (by
    have : h ∈ P ⊓ Subgroup.normalizer (L : Set G) := by rw [hPΦ]; exact h0
    exact this.2)
  have hPM' : ∀ x ∈ P, x ∈ Subgroup.normalizer (L : Set G) → x ∈ Φ := fun x hxP hxM => by
    show x ∈ Φ
    rw [← hPΦ]
    exact ⟨hxP, hxM⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hOH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  have hUV : U ⊓ V = Q ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hidx' : (V ⊓ Q).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
  obtain ⟨v, hvV, hvO⟩ := IsConcreteLE.not_le_iff_exists.mp hVO
  have hv2 := hV2 v hvV
  have hvH : v ∈ H := hTH (hVT hvV)
  have hVL := le_pCoreOf_L hyp hVT hV2
  obtain ⟨m, hmv, hmP, hmcomm, hminv⟩ := exists_inv_conj_frattini h331 hyp hHs hsol hp hp2 hPp
    hPH hPi hHPT hPΦ hVT hTV hVL hidx' hP1 hvV hv2 hvO
  have hmH : m ∈ H := by
    have := H.mul_mem (hOH hmv) hvH
    simpa using this
  have hmP' : ∀ x ∈ P, m * x * m⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmP x).mp hx
  have hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G) := fun g hg =>
    exists_mul_mem_normalizer h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hg
  have hHΦ := le_normalizer_frattini_sup hPH hHO hOH hfr
  have hΦL : Φ ≤ Subgroup.normalizer (L : Set G) := by
    show Φ ≤ _
    rw [← hPΦ]
    exact inf_le_right
  set R := pCoreOf 2 L ⊓ H with hR
  have hR2 : IsPGroup 2 ↥R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have hΦR : Φ ≤ Subgroup.normalizer (R : Set G) := fun f hf =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hΦL hf),
        Subgroup.le_normalizer (hPH (hΦP hf))⟩
  have hVΦ : ∀ x ∈ V, ∀ f ∈ Φ, x * f * x⁻¹ * f⁻¹ ∈ Q := fun x hx f hf =>
    comm_mem_of_le_normalizer hp hp2 hPp hPH hHO hHΦ hR2 inf_le_right hΦR
      ⟨hVL hx, hTH (hVT hx)⟩ hf
  set A := Q ⊓ Subgroup.centralizer (Q : Set G) with hA
  have hA2 : IsPGroup 2 ↥A := hO2.to_le inf_le_left
  have hHA : H ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO hg, B6.le_normalizer_centralizer hHO hg⟩
  have hcV : ∀ w ∈ A, w * (m * w * m⁻¹)⁻¹ ∈ V := by
    intro w hwA
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Q, r * v = m := ⟨m * v⁻¹, hmv, by group⟩
    have hvw : v * w * v⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hHA hvH) w).mp hwA
    have hrc : r * (v * w * v⁻¹) * r⁻¹ = v * w * v⁻¹ := by
      have := (Subgroup.mem_centralizer_iff.mp hvw.2) r hr
      rw [this, mul_inv_cancel_right]
    have e : w * (r * v * w * (r * v)⁻¹)⁻¹ = w * v * w⁻¹ * v⁻¹ := by
      have e1 : r * v * w * (r * v)⁻¹ = r * (v * w * v⁻¹) * r⁻¹ := by group
      rw [e1, hrc]
      group
    rw [e]
    have hwV : w * v * w⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hTV (hQT hwA.1)) v).mp hvV
    exact V.mul_mem hwV (V.inv_mem hvV)
  have hcent : A ⊓ Subgroup.centralizer (Φ : Set G) ≤ Subgroup.centralizer (P : Set G) :=
    le_centralizer_of_inv_frattini hp hp2 hPp hPnc hPΦ hA2 (fun x hx => hHA (hPH hx)) hmP hminv
      (fun w hwA hw1 => hNE _ (hcV w hwA) hw1)
  have hmA : ∀ w ∈ A, m * w * m⁻¹ ∈ A := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHA hmH) w).mp hw
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  let ψ : ↥A →* ↥A :=
    { toFun := fun w => ⟨w * (m * w * m⁻¹)⁻¹, A.mul_mem w.2 (A.inv_mem (hmA w w.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (a : G) * b * (m * (a * b) * m⁻¹)⁻¹ =
          (a * (m * a * m⁻¹)⁻¹) * (b * (m * b * m⁻¹)⁻¹)
        have h1 : (b : G) * (m * b * m⁻¹)⁻¹ * (m * a * m⁻¹)⁻¹ =
            (m * a * m⁻¹)⁻¹ * (b * (m * b * m⁻¹)⁻¹) :=
          hAc _ (A.mul_mem b.2 (A.inv_mem (hmA b b.2))) _ (A.inv_mem (hmA a a.2))
        calc (a : G) * b * (m * (a * b) * m⁻¹)⁻¹
            = a * ((b * (m * b * m⁻¹)⁻¹) * (m * a * m⁻¹)⁻¹) := by group
          _ = a * ((m * a * m⁻¹)⁻¹ * (b * (m * b * m⁻¹)⁻¹)) := by rw [h1]
          _ = (a * (m * a * m⁻¹)⁻¹) * (b * (m * b * m⁻¹)⁻¹) := by group) }
  set X := ψ.range.map A.subtype with hX
  have hXmem : ∀ x ∈ X, ∃ w ∈ A, x = w * (m * w * m⁻¹)⁻¹ := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, w.2, rfl⟩
  have hXV : X ≤ V := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := hXmem x hx
    exact hcV w hw
  have hXA : X ≤ A := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := hXmem x hx
    exact A.mul_mem hw (A.inv_mem (hmA w hw))
  have hXmk : ∀ w ∈ A, w * (m * w * m⁻¹)⁻¹ ∈ X := fun w hw =>
    ⟨ψ ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
  have hΦX : Φ ≤ Subgroup.normalizer (X : Set G) := by
    intro f hf
    have hfH : f ∈ H := hPH (hΦP hf)
    have hfA : ∀ w ∈ A, f * w * f⁻¹ ∈ A := fun w hw =>
      (Subgroup.mem_normalizer_iff.mp (hHA hfH) w).mp hw
    have hfm : f * m = m * f := (hmcomm f hf).symm
    refine Sec121Swap.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨w, hw, rfl⟩ := hXmem x hx
    have hc : f * (m * w * m⁻¹) * f⁻¹ = m * (f * w * f⁻¹) * m⁻¹ := by
      calc f * (m * w * m⁻¹) * f⁻¹ = (f * m) * w * (f * m)⁻¹ := by group
        _ = (m * f) * w * (m * f)⁻¹ := by rw [hfm]
        _ = m * (f * w * f⁻¹) * m⁻¹ := by group
    have e : f * (w * (m * w * m⁻¹)⁻¹) * f⁻¹ =
        f * w * f⁻¹ * (m * (f * w * f⁻¹) * m⁻¹)⁻¹ := by
      rw [← hc]
      group
    rw [e]
    exact hXmk _ (hfA w hw)
  have hXC : X ⊓ Subgroup.centralizer (Φ : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxC⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxP : P ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hcent ⟨hXA hxX, hxC⟩)) y hy)
    exact hhΦ (hPM' h hhP (hNE x (hXV hxX) hx1 (hxP hhP)))
  have hVQ : V ⊓ Q ≠ ⊥ := by
    intro h0
    have h1 := hidx'
    rw [h0, Subgroup.relIndex_bot_left] at h1
    obtain ⟨hn, hcardV, -⟩ := hC
    rw [hcardV] at h1
    rcases hn with rfl | rfl | rfl <;> norm_num at h1
  obtain ⟨z, hzVQ, hz1, hzc⟩ := exists_ne_one_mem_centralizer hO2 inf_le_right
    (fun r hr => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTV (hQT hr), hHO (hTH (hQT hr))⟩)
    hVQ
  have hzA : z ∈ A := ⟨hzVQ.2, hzc⟩
  have hX1 : X ≠ ⊥ := by
    intro hXb
    have hmw : ∀ w ∈ A, m * w * m⁻¹ = w := by
      intro w hw
      have := hXmk w hw
      rw [hXb, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this.symm
    apply hhΦ
    have hPΦ' : ∀ x ∈ P, x ∈ Φ := by
      intro x hx
      obtain ⟨f, hf, hfe⟩ : ∃ f ∈ Φ, m * x * m⁻¹ = f * x⁻¹ :=
        ⟨m * x * m⁻¹ * x, hminv x hx, by group⟩
      have hxz : x * z * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hHA (hPH hx)) z).mp hzA
      have h1 := hmw _ hxz
      have h2 : m * (x * z * x⁻¹) * m⁻¹ = (m * x * m⁻¹) * (m * z * m⁻¹) * (m * x * m⁻¹)⁻¹ := by
        group
      rw [h2, hmw z hzA, hfe] at h1
      have hg : x⁻¹ * f * x⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x⁻¹ * f * x⁻¹ * z = x⁻¹ * ((f * x⁻¹) * z * (f * x⁻¹)⁻¹) * x * (x⁻¹ * f * x⁻¹) := by
              group
          _ = x⁻¹ * (x * z * x⁻¹) * x * (x⁻¹ * f * x⁻¹) := by rw [h1]
          _ = z * (x⁻¹ * f * x⁻¹) := by group
      have hgP : x⁻¹ * f * x⁻¹ ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hx) (hΦP hf)) (P.inv_mem hx)
      have hgΦ := hPM' _ hgP (hNE z hzVQ.1 hz1 hg)
      have hx2 : x ^ 2 ∈ Φ := by
        have h3 : x⁻¹ * f * x ∈ Φ := by
          have := conj_mem_frattini (Subgroup.le_normalizer (P.inv_mem hx)) hf
          rwa [inv_inv] at this
        have e : x ^ 2 = (x⁻¹ * f * x⁻¹)⁻¹ * (x⁻¹ * f * x) := by
          rw [pow_two]
          group
        rw [e]
        exact Φ.mul_mem (Φ.inv_mem hgΦ) h3
      obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
      have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact (Subgroup.zpowers_le.mpr hx2) (mem_zpowers_sq hp hp2 hk')
    exact hPΦ' h hhP
  have hΦV : Φ ≤ Subgroup.normalizer (V : Set G) := by
    intro f hf
    rcases h1216 G T L V hyp hNE f with h1 | h1
    · have hmap : V.map (MulAut.conj f⁻¹).toMonoidHom = V := h1
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hy' : y ∈ V.map (MulAut.conj f⁻¹).toMonoidHom := by rw [hmap]; exact hy
        obtain ⟨y', hy'V, hy'e⟩ := hy'
        change f⁻¹ * y' * f⁻¹⁻¹ = y at hy'e
        have e : f * y * f⁻¹ = y' := by rw [← hy'e]; group
        rw [e]
        exact hy'V
      · intro hy
        have h2 : (MulAut.conj f⁻¹).toMonoidHom (f * y * f⁻¹) ∈
            V.map (MulAut.conj f⁻¹).toMonoidHom := ⟨_, hy, rfl⟩
        rw [hmap] at h2
        change f⁻¹ * (f * y * f⁻¹) * f⁻¹⁻¹ ∈ V at h2
        have e : f⁻¹ * (f * y * f⁻¹) * f⁻¹⁻¹ = y := by group
        rwa [e] at h2
    · exfalso
      apply hX1
      rw [eq_bot_iff, ← h1]
      intro x hx
      refine ⟨hXV hx, ?_⟩
      have hfX : f * x * f⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hΦX hf) x).mp hx
      refine ⟨f * x * f⁻¹, hXV hfX, ?_⟩
      change f⁻¹ * (f * x * f⁻¹) * f⁻¹⁻¹ = x
      group
  exact ⟨hΦV, hVΦ, hcent, X, hX1, le_inf hXV hXA, hΦX, hXC⟩

end Lem22

end CFSG.Quasithin.H13
