module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Assembly
public import CFSG.Quasithin.EmptyFaithful.SzF53Dich2
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Hss36NatAt (H M : Subgroup G) : Prop :=
  ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = true → ⁅Zv α, Zv α'⁆ = ⊥ →
    IsNatSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β) →
    bMin H M = 3

@[expose] def Hss35OrthAt (H M : Subgroup G) : Prop :=
  ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = true → ⁅Zv α, Zv α'⁆ = ⊥ →
    IsOrthSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β) →
    bMin H M ≤ 3

theorem bMin_eq_three_of_le (hA : F53Amalgam H M S) (h34 : Hss34At H M) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hα : vtype α = true) (hz : ⁅Zv α, Zv α'⁆ = ⊥)
    (hle : bMin H M ≤ 3) : bMin H M = 3 := by
  have hb1 := (h34 α β α' hc hα hz).2.2.1
  obtain ⟨-, hodd, -⟩ := hss114_ab hA hc hz hb1
  obtain ⟨k, hk⟩ := hodd
  omega

theorem hss36At_of (hA : F53Amalgam H M S) (h34 : Hss34At H M) (h36n : Hss36NatAt H M)
    (h35o : Hss35OrthAt H M) : Hss36At H M := by
  intro α β α' hc hα hz
  rcases (h34 α β α' hc hα hz).2.2.2 with hn | ho
  · exact h36n α β α' hc hα hz hn
  · exact bMin_eq_three_of_le hA h34 hc hα hz (h35o α β α' hc hα hz ho)

theorem f53DichAt2_of_steps (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h32 : Hss32At H M)
    (h33 : Hss33At H M) (h34 : Hss34At H M) (h36 : Hss36At H M) (h41 : Hss41At H M)
    (h42 : Hss42At H M) (h43 : Hss43At H M) : F53DichAt2 H M where
  s3_range α hαb hα := by
    obtain ⟨β, hαβ⟩ := exists_adj α
    obtain ⟨α', hc⟩ := exists_critData hA hαb hαβ
    by_cases hz : ⁅Zv α, Zv α'⁆ = ⊥
    · have := h36 α β α' hc hα hz
      omega
    · have := h33 α β α' hc hα hz
      omega
  zv_central α β hαβ hαb := by
    cases hα : vtype α with
    | true => exact h32 α β hαβ hα hαb
    | false => exact h41 α β hαβ hα hαb (lt_bAt_of_s5 hA h32 hαβ hα hαb)
  s5_module α hαb hα := by
    have hnb : ∀ β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bMin H M < bAt β :=
      fun β hαβ => lt_bAt_of_s5 hA h32 hαβ hα hαb
    have h1 := h42 α hα hαb hnb
    refine ⟨h1, fun hb => ?_⟩
    rcases h1 with ho | hn
    · have := h43 α hα hαb hnb ho
      omega
    · exact hn
  s3_three α β hαβ hαb hα hb3 := by
    obtain ⟨α', hc⟩ := exists_critData hA hαb hαβ
    have hz : ⁅Zv α, Zv α'⁆ = ⊥ := by
      by_contra hz
      have := h33 α β α' hc hα hz
      omega
    have h4 := h34 α β α' hc hα hz
    exact ⟨h28 (by omega) α β hαβ hαb, h4.2.1, h4.2.2.2⟩

end F53.Stellmacher

@[expose] def F53.Stellmacher.Hss36Nat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S →
    F53.Stellmacher.Hss36NatAt H M

@[expose] def F53.Stellmacher.Hss35Orth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S →
    F53.Stellmacher.Hss35OrthAt H M

end CFSG.Quasithin
