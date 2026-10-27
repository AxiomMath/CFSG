module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre44b
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BCore
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre41b
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre44a

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem eq_one_of_two_odd {V N : Subgroup G} (hV : IsPGroup 2 V) (hNodd : Odd (Nat.card N))
    {u : G} (huV : u ∈ V) (huN : u ∈ N) : u = 1 := by
  obtain ⟨k, hk⟩ := hV ⟨u, huV⟩
  have hk' : u ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf u ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N huN
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun hd => by
      have := Nat.odd_iff.1 hNodd
      omega
  have h3 : orderOf u ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem conj_mem_cen {g x β : G} (hx : x ∈ Cen β) : g * x * g⁻¹ ∈ Cen (g * β * g⁻¹) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc g * x * g⁻¹ * (g * β * g⁻¹) = g * (x * β) * g⁻¹ := by group
    _ = g * (β * x) * g⁻¹ := by rw [hx]
    _ = g * β * g⁻¹ * (g * x * g⁻¹) := by group

theorem conj_odd_normal {β : G} {N : Subgroup G} (g : G)
    (hN : ∀ c ∈ Cen β, ∀ y ∈ N, c * y * c⁻¹ ∈ N) :
    ∀ c ∈ Cen (g * β * g⁻¹), ∀ y ∈ N.map (MulAut.conj g).toMonoidHom,
      c * y * c⁻¹ ∈ N.map (MulAut.conj g).toMonoidHom := by
  intro c hc y hy
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
  have hc' : g⁻¹ * c * g ∈ Cen β := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    calc (g⁻¹ * c * g) * β = g⁻¹ * (c * (g * β * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * β * g⁻¹) * c) * g := by rw [hc]
      _ = β * (g⁻¹ * c * g) := by group
  refine Subgroup.mem_map.2 ⟨(g⁻¹ * c * g) * y₀ * (g⁻¹ * c * g)⁻¹, hN _ hc' y₀ hy₀, ?_⟩
  simp [MulAut.conj_apply]
  group

theorem S44_X_trivial (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) (h41 : Opp 3 (Cen b) ≤ Opp 3 (Cen (b * b₁)))
    (hodd : Odd (Nat.card (Opp 3 (Cen (b * b₁))))) : Opp 3 (Cen b) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := Subgroup.closure ({b, b₁} : Set G) with hE
  set X := Opp 3 (Cen b) with hX
  set Y := Opp 3 (Cen (b * b₁)) with hY
  haveI := isElemAb_E h
  obtain ⟨-, -, -, ⟨i, hiN, hib, hib₁, hib₂⟩, ⟨s, hsN, hsb, hsb₁, hsb₂⟩, -⟩ := h.mono
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  have hYc : Nat.Coprime (Nat.card Y) 6 := by
    have h2 : Nat.Coprime (Nat.card Y) 2 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun hd => ?_)
      have := Nat.odd_iff.1 hodd
      omega
    have h3 : Nat.Coprime (Nat.card Y) 3 := (FF79.L14.Opp_coprime 3 (Cen (b * b₁))).symm
    simpa using Nat.Coprime.mul_right h2 h3
  have hYo : ∀ y ∈ Y, Nat.Coprime (orderOf y) 6 := fun y hy =>
    Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard Y hy) hYc
  have hXY : X ≤ Y := h41
  have hXodd : Odd (Nat.card X) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hXY)
  have hXb₁ : X ≤ Cen b₁ := S41_cen_X hA h
  have hXB : X ≤ CenS B := X_le_cenS_B hA h
  have hXL : X ≤ CenS L := X_le_cenS_L h.hyp hA
  have hXn : ∀ c ∈ Cen b, ∀ x ∈ X, c * x * c⁻¹ ∈ X := fun c hc x hx =>
    FF79.L14.Opp_conj_mem hc hx
  have hYn : ∀ c ∈ Cen (b * b₁), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := fun c hc y hy =>
    FF79.L14.Opp_conj_mem hc hy
  have hs'b : s⁻¹ * b * s = b₁ := by rw [← hsb₁]; group
  have hs'b₁ : s⁻¹ * b₁ * s = b := by rw [← hsb]; group
  have hX₁le : X.map (MulAut.conj s).toMonoidHom ≤ X := by
    refine le_X hA h ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have := conj_mem_cen (g := s) (hXb₁ hx)
      rw [hsb₁] at this
      exact this
    · rintro _ ⟨x, hx, rfl⟩
      have hz : s⁻¹ * (b₁ * b₂) * s ∈ B := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hsN) (b₁ * b₂)).1
          (mul_mem (mem_b₁ h) (mem_b₂ h))
        simpa using this
      have hxz : x ∈ Cen (s⁻¹ * (b₁ * b₂) * s) :=
        Subgroup.mem_centralizer_singleton_iff.2
          ((Subgroup.mem_centralizer_iff.1 (hXB hx) _ hz).symm)
      have := conj_mem_cen (g := s) hxz
      rwa [show s * (s⁻¹ * (b₁ * b₂) * s) * s⁻¹ = b₁ * b₂ by group] at this
    · rintro _ ⟨x, hx, rfl⟩
      show Nat.Coprime (orderOf (MulAut.conj s x)) 6
      rw [MulEquiv.orderOf_eq (MulAut.conj s) x]
      exact hYo x (hXY hx)
    · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
      exact FF79.L14.Opp_coprime 3 (Cen b)
    · intro c hc w hw
      have hcb₁ : c ∈ Cen b₁ := Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 b₁ hb₁L).symm
      have hn := conj_odd_normal (β := b) (N := X) s hXn
      rw [hsb] at hn
      exact hn c hcb₁ w hw
  have hX₁eq : X.map (MulAut.conj s).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hX₁le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj s).injective])
  have hN₂ : ∀ c ∈ Cen b₁, ∀ y ∈ X, c * y * c⁻¹ ∈ X := by
    have hn := conj_odd_normal (β := b) (N := X) s hXn
    rw [hsb, hX₁eq] at hn
    exact hn
  set m : G := s * i * s⁻¹ with hm
  have hmb : m * b * m⁻¹ = b := by
    calc m * b * m⁻¹ = s * (i * (s⁻¹ * b * s) * i⁻¹) * s⁻¹ := by rw [hm]; group
      _ = b := by rw [hs'b, hib₁, hsb₁]
  have hmb₁ : m * b₁ * m⁻¹ = b₁⁻¹ := by
    calc m * b₁ * m⁻¹ = s * (i * (s⁻¹ * b₁ * s) * i⁻¹) * s⁻¹ := by rw [hm]; group
      _ = s * (i * b * i⁻¹) * s⁻¹ := by rw [hs'b₁]
      _ = s * b⁻¹ * s⁻¹ := by rw [hib]
      _ = (s * b * s⁻¹)⁻¹ := by group
      _ = b₁⁻¹ := by rw [hsb]
  have hb₁inv : b₁⁻¹ = b₁ ^ 2 :=
    (eq_inv_of_mul_eq_one_right (by
      rw [← pow_succ']; exact pow3_of_mem h (mem_b₁ h))).symm
  have hmbb₁ : m * (b * b₁) * m⁻¹ = b * b₁ ^ 2 := by
    calc m * (b * b₁) * m⁻¹ = (m * b * m⁻¹) * (m * b₁ * m⁻¹) := by group
      _ = b * b₁ ^ 2 := by rw [hmb, hmb₁, hb₁inv]
  have hmcen : m ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 (by
    calc m * b = (m * b * m⁻¹) * m := by group
      _ = b * m := by rw [hmb])
  have hXY' : X ≤ Y.map (MulAut.conj m).toMonoidHom := by
    intro x hx
    refine Subgroup.mem_map.2 ⟨m⁻¹ * x * m, hXY ?_, ?_⟩
    · have := hXn m⁻¹ (inv_mem hmcen) x hx
      simpa using this
    · simp [MulAut.conj_apply]
      group
  have hYn' : ∀ c ∈ Cen (b * b₁ ^ 2), ∀ y ∈ Y.map (MulAut.conj m).toMonoidHom,
      c * y * c⁻¹ ∈ Y.map (MulAut.conj m).toMonoidHom := by
    have hn := conj_odd_normal (β := b * b₁) (N := Y) m hYn
    rw [hmbb₁] at hn
    exact hn
  have hYodd' : Odd (Nat.card (Y.map (MulAut.conj m).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]; exact hodd
  obtain ⟨-, hKmod, hKsup, -, hKcen⟩ := h.hK
  have hKle : K ≤ L ⊓ Cen b₁ := hKsup ▸ le_sup_right
  obtain ⟨e5⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_equiv_a5_of_psl hKmod
  have h2K : 2 ∣ Nat.card K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
    have h2 : Nat.card (↥K ⧸ Subgroup.center ↥K) = 60 := by
      rw [Nat.card_congr e5.toEquiv, card_alt5]
    rw [h1, h2]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2K
  set t : G := (t' : G) with ht
  have htord : orderOf t = 2 := by rw [ht, Subgroup.orderOf_coe]; exact ht'
  have htL : t ∈ L := (Subgroup.mem_inf.1 (hKle t'.2)).1
  have htb₁ : t * b₁ = b₁ * t := Subgroup.mem_centralizer_singleton_iff.1 (hKcen t'.2)
  have htb : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.1 (h.hyp.hLC htL)
  have ht1 : t ≠ 1 := fun he => by rw [he, orderOf_one] at htord; omega
  set T : Subgroup G := Subgroup.zpowers t with hT
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [hT, Nat.card_zpowers, htord]; norm_num)
  have hT1 : T ≠ ⊥ := fun he => ht1 (Subgroup.mem_bot.1 (he ▸ Subgroup.mem_zpowers t))
  set V : Subgroup G := Op 2 (Nor T) with hV
  have hV2 : IsPGroup 2 V := FF79.L41.Op_isPGroup (p := 2) (Nor T)
  have hnorV : ∀ g : G, g * t = t * g → g ∈ Nor V := fun g hg =>
    nor_Op (p := 2) (nor_zpowers hg)
  have hEc : E ≤ Subgroup.centralizer ({t} : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro z (rfl | hz)
    · exact Subgroup.mem_centralizer_singleton_iff.2 htb.symm
    · rw [Set.mem_singleton_iff.1 hz]
      exact Subgroup.mem_centralizer_singleton_iff.2 htb₁.symm
  have hEV : E ≤ Nor V := fun e he =>
    hnorV e (Subgroup.mem_centralizer_singleton_iff.1 (hEc he))
  have hXt : ∀ x ∈ X, x * t = t * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (hXL hx) t htL).symm
  have hXV : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.1 (hnorV x (hXt x hx)) v).1 hv
  have hgen : V ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), V ⊓ Cen a :=
    B_gen_centralizers (E := E) (X := V) (card_E_ge h) hV2 hEV
  have hVX : V ≤ Subgroup.centralizer (X : Set G) := by
    refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
    have key : ∀ β : G, ∀ N : Subgroup G, X ≤ N → (∀ c ∈ Cen β, ∀ y ∈ N, c * y * c⁻¹ ∈ N) →
        Odd (Nat.card N) → V ⊓ Cen β ≤ Subgroup.centralizer (X : Set G) := by
      intro β N hXN hN hNodd v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (comm_of_odd_normal hXN hN hNodd hV2 hXV v hv x hx).symm
    rcases E_four h ha ha1 with h1 | h1 | h1 | h1
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans (key b X le_rfl hXn hXodd)
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans (key b₁ X le_rfl hN₂ hXodd)
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans (key (b * b₁) Y hXY hYn hodd)
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans
        (key (b * b₁ ^ 2) _ hXY' hYn' hYodd')
  have hXV' : X ≤ Nor T ⊓ CenS V := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨nor_zpowers (hXt x hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hVX hv) x hx).symm
  have hXle : X ≤ V := fun x hx => B_charTwo h.hyp.char2 hT2 hT1 (hXV' hx)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact eq_one_of_two_odd hV2 hXodd (hXle hx) hx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
