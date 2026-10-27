module

public import CFSG.Quasithin.H13.L32NLem1444h
public import CFSG.Quasithin.EmptyFaithful.SBc8Transfer

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [Finite G]

namespace Setup4

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem eq_of_mem_V1 {a b : G} (ha : a ∈ fsuV1 T V) (ha1 : a ≠ 1) (hb : b ∈ fsuV1 T V)
    (hb1 : b ≠ 1) : a = b := by
  obtain ⟨z₀, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp S.card2
  have h1 := huniq ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
  have h2 := huniq ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem comm_V1 {h : G} (hh : h ∈ l32nH T V) {x : G} (hx : x ∈ fsuV1 T V) : h * x * h⁻¹ = x := by
  by_cases hx1 : x = 1
  · rw [hx1]
    group
  have hhx : h * x * h⁻¹ ∈ fsuV1 T V := (Subgroup.mem_normalizer_iff.mp hh x).mp hx
  refine S.eq_of_mem_V1 hhx (fun h1 => hx1 ?_) hx hx1
  calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
    _ = 1 := by rw [h1]; group

theorem cent_le_H : Subgroup.centralizer (fsuU T V : Set G) ≤ l32nH T V := by
  intro d hd
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
  exact Subgroup.mem_centralizer_iff.mp hd v (V_le_U (S.plane.1.1 (S.plane.2 hv)))

theorem cent_le_Q : Subgroup.centralizer (fsuU T V : Set G) ≤ pCoreOf 2 (l32nH T V) := by
  intro d hd
  have hdH := S.cent_le_H hd
  have hdN : d ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    Subgroup.centralizer_le_normalizer _ hd
  rw [← S.cHat]
  refine (L14332.rho_eq_one_iff_mem (D := D) hdH hdN).mp (LinearEquiv.ext fun w => ?_)
  obtain ⟨u, hu, rfl⟩ := D.π_surj w
  rw [D.ρ_π _ u hu]
  have : d * u * d⁻¹ = u := by
    rw [← Subgroup.mem_centralizer_iff.mp hd u hu]
    group
  simp [this]

theorem cent_le_T : Subgroup.centralizer (fsuU T V : Set G) ≤ T := S.cent_le_Q.trans S.QT

theorem cent_le_normL : Subgroup.centralizer (fsuU T V : Set G) ≤
    Subgroup.normalizer (L : Set G) := by
  intro d hd
  refine S.normVL (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_))
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp hd v (V_le_U hv)

theorem comm_mem_V {d : G} (hd : d ∈ Subgroup.centralizer (fsuU T V : Set G)) {l : G}
    (hl : l ∈ L) : l * d * l⁻¹ * d⁻¹ ∈ V := by
  have hdV : ∀ v ∈ V, d * v * d⁻¹ = v := fun v hv => by
    rw [← Subgroup.mem_centralizer_iff.mp hd v (V_le_U hv)]
    group
  rw [← S.centL]
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  · have h1 : d * l⁻¹ * d⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (S.cent_le_normL hd) _).mp (L.inv_mem hl)
    rw [show l * d * l⁻¹ * d⁻¹ = l * (d * l⁻¹ * d⁻¹) by group]
    exact L.mul_mem hl h1
  · have hlv : l⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem
        (S.L_le_normV hl)) v).mp hv
      simpa using this
    have h1 : d⁻¹ * (l⁻¹ * v * l) * d = l⁻¹ * v * l := by
      calc d⁻¹ * (l⁻¹ * v * l) * d = d⁻¹ * (d * (l⁻¹ * v * l) * d⁻¹) * d := by
            rw [hdV _ hlv]
        _ = l⁻¹ * v * l := by group
    have h2 : (l * d * l⁻¹ * d⁻¹)⁻¹ * v * (l * d * l⁻¹ * d⁻¹) = v := by
      calc (l * d * l⁻¹ * d⁻¹)⁻¹ * v * (l * d * l⁻¹ * d⁻¹) =
          d * (l * (d⁻¹ * (l⁻¹ * v * l) * d) * l⁻¹) * d⁻¹ := by group
        _ = d * v * d⁻¹ := by rw [h1]; group
        _ = v := hdV v hv
    calc v * (l * d * l⁻¹ * d⁻¹) =
        l * d * l⁻¹ * d⁻¹ * ((l * d * l⁻¹ * d⁻¹)⁻¹ * v * (l * d * l⁻¹ * d⁻¹)) := by group
      _ = l * d * l⁻¹ * d⁻¹ * v := by rw [h2]

theorem comm_conj_mem {d : G} (hd : d ∈ Subgroup.centralizer (fsuU T V : Set G)) {l : G}
    (hl : l ∈ L) {u : G} (hu : u ∈ fsuU T V) :
    l * (d * (l⁻¹ * u * l) * d⁻¹ * (l⁻¹ * u * l)⁻¹) * l⁻¹ ∈ fsuV1 T V := by
  have hn : d * l * d⁻¹ * l⁻¹ ∈ V := by
    have := V.inv_mem (S.comm_mem_V hd hl)
    simpa [mul_assoc] using this
  set n := d * l * d⁻¹ * l⁻¹ with hndef
  have hdu : d⁻¹ * u * d = u := by
    have h1 := Subgroup.mem_centralizer_iff.mp hd u hu
    calc d⁻¹ * u * d = d⁻¹ * (u * d) := by group
      _ = d⁻¹ * (d * u) := by rw [h1]
      _ = u := by group
  have e : l * (d * (l⁻¹ * u * l) * d⁻¹ * (l⁻¹ * u * l)⁻¹) * l⁻¹ = n⁻¹ * u * n⁻¹⁻¹ * u⁻¹ := by
    rw [hndef]
    calc l * (d * (l⁻¹ * u * l) * d⁻¹ * (l⁻¹ * u * l)⁻¹) * l⁻¹ =
        l * d * l⁻¹ * u * l * d⁻¹ * l⁻¹ * u⁻¹ := by group
      _ = l * d * l⁻¹ * d⁻¹ * (d * u * d⁻¹) * d * l * d⁻¹ * l⁻¹ * u⁻¹ := by group
      _ = (d * l * d⁻¹ * l⁻¹)⁻¹ * u * (d * l * d⁻¹ * l⁻¹)⁻¹⁻¹ * u⁻¹ := by
          rw [show d * u * d⁻¹ = u by
            calc d * u * d⁻¹ = d * (d⁻¹ * u * d) * d⁻¹ := by rw [hdu]
              _ = u := by group]
          group
  rw [e, ← S.zU]
  exact comm_mem_centerOf S.ext _ ((fsuU T V).inv_mem (V_le_U hn)) _ hu

theorem exists_conj_of_mem_Wg :
    ∃ l ∈ L, (∀ w ∈ CFSG.conjugate (l32nW T V V₂) g, l * w * l⁻¹ ∈ fsuU T V) ∧
      ∀ x ∈ fsuV1 T V, l⁻¹ * x * l ∈ fsuV1 T V → x = 1 := by
  have hg : g ∈ ((L ⊔ T : Subgroup G) : Set G) := S.gP.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ S.TL] at hg
  obtain ⟨l₀, hl₀, t₀, ht₀, hg'⟩ := hg
  have hg'' : l₀ * t₀ = g := hg'
  have ht₀H : t₀ ∈ l32nH T V := S.TH ht₀
  refine ⟨t₀⁻¹ * l₀ * t₀, ?_, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (S.TL ht₀)) l₀).mp
      hl₀
    simpa using this
  · rintro _ ⟨w, hw, rfl⟩
    have hwU : w ∈ fsuU T V := hw.1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hg'']
    have e : t₀⁻¹ * l₀ * t₀ * ((l₀ * t₀)⁻¹ * w * (l₀ * t₀)) * (t₀⁻¹ * l₀ * t₀)⁻¹ =
        t₀⁻¹ * w * t₀⁻¹⁻¹ := by group
    rw [e]
    exact L128A.HatU.conj_mem (L14332.l32nH_le_normalizer_fsuU T V
      ((l32nH T V).inv_mem ht₀H)) hwU
  · intro x hx hxl
    by_contra hx1
    apply S.gH
    set l := t₀⁻¹ * l₀ * t₀ with hldef
    have hgl : g = t₀ * l := by rw [hldef, ← hg'']; group
    have hxl1 : l⁻¹ * x * l ≠ 1 := fun h1 => hx1 (by
      calc x = l * (l⁻¹ * x * l) * l⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    have hlx : l⁻¹ * x * l = x := S.eq_of_mem_V1 hxl hxl1 hx hx1
    have htx : t₀⁻¹ * x * t₀ = x := by
      have := S.comm_V1 ((l32nH T V).inv_mem ht₀H) hx
      simpa using this
    have hgx : g⁻¹ * x * g = x := by
      rw [hgl]
      calc (t₀ * l)⁻¹ * x * (t₀ * l) = l⁻¹ * (t₀⁻¹ * x * t₀) * l := by group
        _ = x := by rw [htx, hlx]
    rw [show l32nH T V = Subgroup.normalizer (fsuV1 T V : Set G) from rfl,
      normalizer_eq_centralizer_of_card_two S.card2 hx hx1,
      Subgroup.mem_centralizer_singleton_iff]
    calc g * x = g * (g⁻¹ * x * g) := by rw [hgx]
      _ = x * g := by group

theorem comm_TL {d : G} (hd : d ∈ Subgroup.centralizer (fsuU T V : Set G)) {p : G}
    (hp : p ∈ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g) : p * d = d * p := by
  obtain ⟨l, hl, hlW, hl1⟩ := S.exists_conj_of_mem_Wg
  have hle : fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g ≤
      Subgroup.centralizer ({d} : Set G) := by
    refine sup_le (fun u hu => ?_) (fun w hw => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hd u hu
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hwL : w ∈ L := S.Wg_le_L hw
      have hwH : w ∈ l32nH T V := S.Wg_le_H hw
      have hwN := L14332.l32nH_le_normalizer_fsuU T V hwH
      set c := d * w * d⁻¹ * w⁻¹ with hcdef
      have hcC : c ∈ Subgroup.centralizer (fsuU T V : Set G) := by
        have h1 : w * d⁻¹ * w⁻¹ ∈ Subgroup.centralizer (fsuU T V : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer'' _ hwN) _).mp
            ((Subgroup.centralizer _).inv_mem hd)
        rw [show c = d * (w * d⁻¹ * w⁻¹) by rw [hcdef]; group]
        exact (Subgroup.centralizer _).mul_mem hd h1
      have hcV : c ∈ V := by
        have := V.inv_mem (S.comm_mem_V hd hwL)
        rw [show c = (w * d * w⁻¹ * d⁻¹)⁻¹ by rw [hcdef]; group]
        exact this
      have hcZ : c ∈ fsuV1 T V := by
        rw [← S.zU]
        exact ⟨V_le_U hcV, hcC⟩
      have hcl : l * c * l⁻¹ ∈ fsuV1 T V := by
        have hu := hlW w hw
        have := S.comm_conj_mem hd hl hu
        rw [show l⁻¹ * (l * w * l⁻¹) * l = w by group] at this
        exact this
      have hc1 : l * c * l⁻¹ = 1 := hl1 _ hcl (by simpa [mul_assoc] using hcZ)
      have hc1' : c = 1 := by
        calc c = l⁻¹ * (l * c * l⁻¹) * l := by group
          _ = 1 := by rw [hc1]; group
      calc w * d = (d * w * d⁻¹ * w⁻¹)⁻¹ * (d * w) := by group
        _ = d * w := by rw [← hcdef, hc1', inv_one, one_mul]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hp)

theorem cent_le_center (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.centralizer (fsuU T V : Set G) ≤ fsuV1 T V := by
  intro d hd
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => S.comm_V hx hy
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using S.elem.2 x x.2)⟩
  have hodd : ¬ 2 ∣ (fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g).relIndex L := by
    rw [S.relIndex_TL]
    decide
  obtain ⟨m, hm, hml⟩ := SBc8.exists_mul_centralizer_of_cocycle S.L_le_normV hVc hV2 S.TL_le_L
    hodd (fun v hv => by rw [← Subgroup.mem_centralizer_iff.mp hd v (V_le_U hv)]; group)
    (fun l hl => S.comm_mem_V hd hl)
    (fun p hp => by rw [S.comm_TL hd hp]; group)
  have hdm : d * m⁻¹ ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem (S.cent_le_T hd) (T.inv_mem (S.QT (S.V_le_Q hm))),
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    calc l * (d * m⁻¹) = l * (d * m⁻¹) * l⁻¹ * l := by group
      _ = d * m⁻¹ * l := by rw [hml l hl]
  rw [hCTL, Subgroup.mem_bot] at hdm
  have hdm' : d = m := by
    calc d = d * m⁻¹ * m := by group
      _ = m := by rw [hdm, one_mul]
  rw [← S.zU]
  exact ⟨V_le_U (hdm' ▸ hm), hd⟩

omit S in
theorem comm_mem_center_of_mem_Q (S : Setup4 G T L V V₂ g D Q₁ Q₂) {q : G}
    (hq : q ∈ pCoreOf 2 (l32nH T V)) {u : G} (hu : u ∈ fsuU T V) :
    q * u * q⁻¹ * u⁻¹ ∈ centerOf (fsuU T V) := by
  have hqH : q ∈ l32nH T V := pCoreOf_le 2 _ hq
  have hqN := L14332.l32nH_le_normalizer_fsuU T V hqH
  have hρ := S.rho_eq_one_of_mem_Q hq hqN
  have hquq : q * u * q⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem hqN hu
  have h1 : D.π (q * u * q⁻¹) = D.π u := by
    rw [← D.ρ_π ⟨q, hqN⟩ u hu, hρ]
    rfl
  have h2 := (D.π_eq_iff _ hquq u hu).mp h1
  have h3 : (u * (q * u * q⁻¹)⁻¹) ∈ centerOf (fsuU T V) := by
    have := (centerOf (fsuU T V)).inv_mem h2
    have e : ((q * u * q⁻¹)⁻¹ * u)⁻¹ = u⁻¹ * (q * u * q⁻¹) := by group
    rw [e] at this
    have hc : u * (u⁻¹ * (q * u * q⁻¹)) * u⁻¹ = u⁻¹ * (q * u * q⁻¹) := by
      rw [Subgroup.mem_centralizer_iff.mp this.2 u hu]
      group
    have h4 : u * (q * u * q⁻¹)⁻¹ = (u * (u⁻¹ * (q * u * q⁻¹)) * u⁻¹)⁻¹ := by group
    rw [h4, hc]
    exact (centerOf (fsuU T V)).inv_mem this
  have := (centerOf (fsuU T V)).inv_mem h3
  simpa [mul_assoc] using this

theorem comm_Q₁_of_comm {q : G} (h1 : Commute q (S.cfg.phiA (QuaternionGroup.a 1)))
    (h2 : Commute q (S.cfg.phiA (QuaternionGroup.xa 0))) {x : G} (hx : x ∈ Q₁) : Commute q x := by
  obtain ⟨u, rfl⟩ := S.cfg.exists_phiA hx
  have ha : ∀ i : ZMod (2 * 2), Commute q (S.cfg.phiA (QuaternionGroup.a i)) := by
    intro i
    have e : (QuaternionGroup.a i : Q8SqE9.Q8) = QuaternionGroup.a 1 ^ i.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [e, map_pow]
    exact h1.pow_right _
  rcases u with i | i
  · exact ha i
  · have e : (QuaternionGroup.xa i : Q8SqE9.Q8) = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [e, map_mul]
    exact h2.mul_right (ha i)

theorem comm_Q₂_of_comm {q : G} (h1 : Commute q (S.cfg.phiB (QuaternionGroup.a 1)))
    (h2 : Commute q (S.cfg.phiB (QuaternionGroup.xa 0))) {x : G} (hx : x ∈ Q₂) : Commute q x := by
  obtain ⟨u, rfl⟩ := S.cfg.exists_phiB hx
  have ha : ∀ i : ZMod (2 * 2), Commute q (S.cfg.phiB (QuaternionGroup.a i)) := by
    intro i
    have e : (QuaternionGroup.a i : Q8SqE9.Q8) = QuaternionGroup.a 1 ^ i.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [e, map_pow]
    exact h1.pow_right _
  rcases u with i | i
  · exact ha i
  · have e : (QuaternionGroup.xa i : Q8SqE9.Q8) = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [e, map_mul]
    exact h2.mul_right (ha i)

theorem exists_hom_comm {u : G} (hu : u ∈ fsuU T V) :
    ∃ ψ : ↥(pCoreOf 2 (l32nH T V)) →* ↥(centerOf (fsuU T V)),
      ∀ q, ((ψ q : ↥(centerOf (fsuU T V))) : G) = q * u * (q : G)⁻¹ * u⁻¹ := by
  refine ⟨{ toFun := fun q => ⟨q * u * (q : G)⁻¹ * u⁻¹, S.comm_mem_center_of_mem_Q q.2 hu⟩
            map_one' := by ext; simp
            map_mul' := fun q q' => ?_ }, fun q => rfl⟩
  apply Subtype.ext
  show (q : G) * q' * u * ((q : G) * q')⁻¹ * u⁻¹ =
    ((q : G) * u * (q : G)⁻¹ * u⁻¹) * ((q' : G) * u * (q' : G)⁻¹ * u⁻¹)
  set A := (q : G) * u * (q : G)⁻¹ * u⁻¹ with hA
  set B := (q' : G) * u * (q' : G)⁻¹ * u⁻¹ with hB
  have hAZ : A ∈ centerOf (fsuU T V) := S.comm_mem_center_of_mem_Q q.2 hu
  have hBZ : B ∈ centerOf (fsuU T V) := S.comm_mem_center_of_mem_Q q'.2 hu
  have hqB : (q : G) * B * (q : G)⁻¹ = B :=
    S.comm_V1 (pCoreOf_le 2 _ q.2) (by rw [← S.zU]; exact hBZ)
  have hAB : A * B = B * A := Subgroup.mem_centralizer_iff.mp hBZ.2 A hAZ.1
  calc (q : G) * q' * u * ((q : G) * q')⁻¹ * u⁻¹ =
      ((q : G) * B * (q : G)⁻¹) * A := by rw [hA, hB]; group
    _ = A * B := by rw [hqB, hAB]

theorem card_Q_le : Nat.card ↥(pCoreOf 2 (l32nH T V)) ≤
    16 * Nat.card ↥(pCoreOf 2 (l32nH T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
  set i₁ := S.cfg.phiA (QuaternionGroup.a 1)
  set j₁ := S.cfg.phiA (QuaternionGroup.xa 0)
  set i₂ := S.cfg.phiB (QuaternionGroup.a 1)
  set j₂ := S.cfg.phiB (QuaternionGroup.xa 0)
  obtain ⟨ψ₁, hψ₁⟩ := S.exists_hom_comm (S.Q₁_le (S.cfg.phiA_mem (QuaternionGroup.a 1)))
  obtain ⟨ψ₂, hψ₂⟩ := S.exists_hom_comm (S.Q₁_le (S.cfg.phiA_mem (QuaternionGroup.xa 0)))
  obtain ⟨ψ₃, hψ₃⟩ := S.exists_hom_comm (S.Q₂_le (S.cfg.phiB_mem (QuaternionGroup.a 1)))
  obtain ⟨ψ₄, hψ₄⟩ := S.exists_hom_comm (S.Q₂_le (S.cfg.phiB_mem (QuaternionGroup.xa 0)))
  set Ψ := ψ₁.prod (ψ₂.prod (ψ₃.prod ψ₄)) with hΨ
  have hker := Subgroup.card_ker_mul_card_range Ψ
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by rw [S.zU, S.card2]
  have hrange : Nat.card Ψ.range ≤ 16 := by
    have := Subgroup.card_le_card_group Ψ.range
    simp only [Nat.card_prod, hZ2] at this
    simpa using this
  have hcomm : ∀ (ψ : ↥(pCoreOf 2 (l32nH T V)) →* ↥(centerOf (fsuU T V))) (x : G),
      (∀ q, ((ψ q : ↥(centerOf (fsuU T V))) : G) = q * x * (q : G)⁻¹ * x⁻¹) →
      ∀ q, ψ q = 1 → Commute (q : G) x := by
    intro ψ x hψ q hq
    have h := hψ q
    rw [hq] at h
    have h' : (q : G) * x * (q : G)⁻¹ * x⁻¹ = 1 := h.symm
    calc (q : G) * x = (q : G) * x * (q : G)⁻¹ * x⁻¹ * (x * q) := by group
      _ = x * q := by rw [h', one_mul]
  have hkerle : Nat.card Ψ.ker ≤
      Nat.card ↥(pCoreOf 2 (l32nH T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun q => ⟨(q : ↥(pCoreOf 2 (l32nH T V))), (q : ↥(pCoreOf 2 (l32nH T V))).2, ?_⟩) ?_
    · have hq : Ψ (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := MonoidHom.mem_ker.mp q.2
      have h1 : ψ₁ (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := congrArg Prod.fst hq
      have h2 : ψ₂ (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := congrArg (fun x => x.2.1) hq
      have h3 : ψ₃ (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := congrArg (fun x => x.2.2.1) hq
      have h4 : ψ₄ (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := congrArg (fun x => x.2.2.2) hq
      have c₁ := hcomm ψ₁ _ hψ₁ _ h1
      have c₂ := hcomm ψ₂ _ hψ₂ _ h2
      have c₃ := hcomm ψ₃ _ hψ₃ _ h3
      have c₄ := hcomm ψ₄ _ hψ₄ _ h4
      have hle' : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer
          ({((q : ↥(pCoreOf 2 (l32nH T V))) : G)} : Set G) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (S.comm_Q₁_of_comm c₁ c₂ hx).eq.symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (S.comm_Q₂_of_comm c₃ c₄ hx).eq.symm
      have hle : ∀ x ∈ fsuU T V,
          x ∈ Subgroup.centralizer ({((q : ↥(pCoreOf 2 (l32nH T V))) : G)} : Set G) :=
        fun x hx => hle' (by rw [S.sup]; exact hx)
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle x hx))
    · intro a b hab
      have h : ((a : ↥(pCoreOf 2 (l32nH T V))) : G) = ((b : ↥(pCoreOf 2 (l32nH T V))) : G) :=
        congrArg (fun x : ↥(pCoreOf 2 (l32nH T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) =>
          (x : G)) hab
      exact Subtype.ext (Subtype.ext h)
  have hQ := hker
  calc Nat.card ↥(pCoreOf 2 (l32nH T V)) = Nat.card Ψ.ker * Nat.card Ψ.range := hQ.symm
    _ ≤ Nat.card ↥(pCoreOf 2 (l32nH T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) * 16 :=
      Nat.mul_le_mul hkerle hrange
    _ = _ := mul_comm _ _

theorem U_eq_Q (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    fsuU T V = pCoreOf 2 (l32nH T V) := by
  have h1 := S.card_Q_le
  have h2 : Nat.card ↥(pCoreOf 2 (l32nH T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) ≤ 2 := by
    rw [← S.card2]
    exact Subgroup.card_le_of_le (inf_le_right.trans (S.cent_le_center hCTL))
  exact Subgroup.eq_of_le_of_card_ge S.U_le_Q (by rw [S.card32]; omega)

end Setup4

end L1444

end CFSG.Quasithin.H13
