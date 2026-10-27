module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.Quasithin

structure HPres {G : Type*} [Group G] (a b x u : G) : Prop where
  r1 : a ^ 4 = 1
  r2 : (x * a * x⁻¹) * (x * a * x⁻¹) * a⁻¹ * a⁻¹ = 1
  r3 : (x * a * x⁻¹) * a * (x * a⁻¹ * x⁻¹) * a = 1
  r4 : a * (x * a * x⁻¹) * (x * x * a⁻¹ * x⁻¹ * x⁻¹) = 1
  r5 : x * x * x = 1
  r6 : b ^ 4 = 1
  r7 : b * b * a⁻¹ * a⁻¹ = 1
  r8 : (x * b * x⁻¹) * (x * b * x⁻¹) * a⁻¹ * a⁻¹ = 1
  r9 : (x * b * x⁻¹) * b * (x * b⁻¹ * x⁻¹) * b = 1
  r10 : b * (x * b * x⁻¹) * (x * x * b⁻¹ * x⁻¹ * x⁻¹) = 1
  r11 : a * b * a⁻¹ * b⁻¹ = 1
  r12 : a * (x * b * x⁻¹) * a⁻¹ * (x * b⁻¹ * x⁻¹) = 1
  r13 : a * (x * x * b * x⁻¹ * x⁻¹) * a⁻¹ * (x * x * b⁻¹ * x⁻¹ * x⁻¹) = 1
  r14 : u * u = 1
  r15 : u * x * u * x = 1
  r16 : u * a * u * (x * a * x⁻¹) = 1
  r17 : u * b * u * (x * b * x⁻¹) = 1

end CFSG.Quasithin
